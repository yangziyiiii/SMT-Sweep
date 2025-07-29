#include "sweeper/sweeper_engine.hpp"
#include <filesystem>
#include <fstream>
#include <set>

using namespace smt;
using namespace std;

namespace sweeper {

void pre_collect_constants(const std::vector<Term>& traversal_roots,
                           std::unordered_map<Term, NodeData>& node_data_map,
                           std::unordered_map<uint32_t, TermVec>& hash_term_map,
                           std::unordered_map<Term, Term>& substitution_map,
                           const int & num_iterations)
{
    std::stack<Term> stack;
    std::unordered_set<Term> visited;
    for (const auto &root : traversal_roots) stack.push(root);

    while (!stack.empty()) {
        Term current = stack.top(); stack.pop();
        if (visited.find(current) != visited.end()) continue;
        visited.insert(current);

        if (substitution_map.find(current) != substitution_map.end()) continue;

        if (current->is_value()) {
            // 常量批量填充仿真数据（BOOL → "1/0"，BV → 去掉 "#b" 前缀）
            if(current->get_sort()->get_sort_kind() == BOOL){
                std::string bitval = (current->to_string() == "true") ? "1" : "0";
                for (int i = 0; i < num_iterations; ++i)
                    node_data_map[current].get_simulation_data().push_back(btor_bv_char_to_bv(bitval.c_str()));
            } else {
                std::string s = current->to_string().substr(2);
                for (int i = 0; i < num_iterations; ++i)
                    node_data_map[current].get_simulation_data().push_back(btor_bv_char_to_bv(s.data()));
            }
            substitution_map.insert({current, current});
            hash_term_map[node_data_map[current].hash()].push_back(current);
            continue;
        }

        for (auto ch : current)
            if (ch->get_sort()->get_sort_kind() == BV || ch->get_sort()->get_sort_kind() == BOOL)
                stack.push(ch);
    }
}

// 后序遍历 + 等价检测（哈希 → 仿真对齐 → 必要时 SAT 验证）
void post_order(const Term & root,
                std::unordered_map<Term, NodeData> & node_data_map,
                std::unordered_map<uint32_t, TermVec> & hash_term_map,
                std::unordered_map<Term, Term> & substitution_map,
                const std::unordered_map<Term, std::unordered_map<std::string, std::string>> & all_luts,
                int & count, int & unsat_count, int & sat_count,
                SmtSolver & solver, int & num_iterations, bool dump_enable,
                const TermVec & input_terms,
                int timeout_ms, bool debug,
                std::string & dump_file_path, std::string & load_file_path,
                std::chrono::milliseconds & total_sat_time,
                std::chrono::milliseconds & total_unsat_time,
                UnorderedTermSet & out)
{
    // 统计总节点
    int total_nodes = 0, processed_nodes = 0;
    count_total_nodes(root, total_nodes);

    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});

    while(!node_stack.empty()) {
        auto & [current, visited] = node_stack.top();

        if(substitution_map.find(current) != substitution_map.end()) {
            node_stack.pop(); continue;
        }

        if(!visited) {
            for(Term child : current) {
                auto k = child->get_sort()->get_sort_kind();
                if(k == BV || k == BOOL) node_stack.push({child,false});
            }
            visited = true;
            continue;
        }

        // children ready
        TermVec children(current->begin(), current->end());

        if(current->is_value()) {
            simulate_constant_node(current, num_iterations, node_data_map);
            substitution_map.insert({current, current});
            hash_term_map[node_data_map[current].hash()].push_back(current);
            processed_nodes++;
            node_stack.pop();
            continue;
        }

        if(current->is_symbolic_const() && current->get_op().is_null()) {
            // 输入：simulation() 已经填好，直接登记
            simulate_leaf_node(current, num_iterations, node_data_map, dump_file_path, load_file_path);
            substitution_map.insert({current, current});
            processed_nodes++;
            node_stack.pop();
            continue;
        }

        // 一般内部节点
        bool substitution_happened = false;
        TermVec children_substituted;
        children_substitution(children, children_substituted, substitution_map);
        if (children_substituted.size() != children.size())
            throw std::runtime_error("children_substitution size mismatch");
        for (size_t i = 0; i < children.size(); ++i)
            if (children_substituted[i] != children[i]) { substitution_happened = true; break; }

        auto op_type = current->get_op();
        Term cnode = substitution_happened ? solver->make_term(op_type, children_substituted) : current;

        NodeData sim_data;
        compute_simulation(children_substituted, num_iterations, op_type, node_data_map, all_luts, sim_data);
        auto current_hash = sim_data.hash();

        TryFindResult result = try_find_equiv_term(cnode, current_hash, sim_data,
                                                   num_iterations, hash_term_map,
                                                   node_data_map, substitution_map, debug);

        if (result.found && result.term_eq) {
            substitution_map.insert({current, result.term_eq});
        } else {
            for (const auto & t : result.terms_for_solving) {
                if (unsat_count >= 30 && sat_count >= 100) break; // 与原实现一致的“停止线”

                solver->push();
                auto eq = solver->make_term(Equal, t, cnode);
                solver->assert_formula(solver->make_term(Not, eq));

                std::ostringstream file_name;
                if (dump_enable) {
                    auto timestamp = std::chrono::high_resolution_clock::now();
                    auto ns = std::chrono::duration_cast<std::chrono::nanoseconds>(timestamp.time_since_epoch()).count();
                    std::filesystem::path dir = std::filesystem::current_path() / "generate";
                    if (!std::filesystem::exists(dir)) std::filesystem::create_directory(dir);
                    file_name << dir.string() << "/" << ns << ".smt2";
                    std::ofstream smt2_file(file_name.str());
                    if (smt2_file.is_open()) {
                        solver->dump_smt2(file_name.str());
                        smt2_file.close();
                    }
                }

                auto start = std::chrono::high_resolution_clock::now();
                solver->push();
                solver->set_opt("time-limit", std::to_string(1));
                auto res = solver->check_sat();
                solver->pop();
                auto end = std::chrono::high_resolution_clock::now();
                auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
                auto elapsed = duration.count();
                count++;

                if (elapsed >= timeout_ms) {
                    std::cout << "t"; std::cout.flush();
                    total_sat_time += duration;
                    solver->pop();
                    continue;
                }

                if (res.is_unsat()) {
                    total_unsat_time += duration;
                    unsat_count++;
                    substitution_map.insert({current, t});
                    if (dump_enable) {
                        std::ofstream smt2_file(file_name.str(), std::ios::app);
                        if (smt2_file.is_open()) { smt2_file << "UNSAT\n"; smt2_file.close(); }
                    }
                    solver->pop();
                    break;
                } else {
                    total_sat_time += duration;
                    sat_count++;
                    if (dump_enable) {
                        std::ofstream smt2_file(file_name.str(), std::ios::app);
                        if (smt2_file.is_open()) { smt2_file << "SAT\n"; smt2_file.close(); }
                    }
                    solver->pop();
                }
            }
        }

        if (substitution_map.find(current) == substitution_map.end()) {
            // 无可替代：登记仿真数据、放入哈希桶
            node_data_map[current] = std::move(sim_data);
            hash_term_map[current_hash].push_back(current);
            substitution_map.insert({current, current});
        }

        processed_nodes++;
        node_stack.pop();
    }

    // 末尾一致化：确保每个节点的仿真向量长度等于 num_iterations
    fill_simulation_data_for_all_nodes(node_data_map, solver, num_iterations, substitution_map, all_luts);
}

} // namespace sweeper
