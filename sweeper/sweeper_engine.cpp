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
                int & count, 
                int & unsat_count, 
                int & sat_count,
                SmtSolver & solver, 
                int & num_iterations, 
                bool dump_enable,
                int timeout_ms, 
                bool debug,
                std::string & dump_file_path, 
                std::string & load_file_path,
                std::chrono::milliseconds & total_sat_time,
                std::chrono::milliseconds & total_unsat_time,
                std::chrono::milliseconds & ordering_time
) {
    // 统计总节点
    int total_nodes = 0, processed_nodes = 0;
    count_total_nodes(root, total_nodes);
    int next_progress_milestone = 5;

    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});

    //——— 配置：样本阈值（可根据需要调整/外传） ———//
    const int NEED_UNSAT = 20;
    const int NEED_SAT   = 1;

     //——— 相位管理 ———//
    bool apply_only = false;        // // false: 相位A（发现）；true: 相位B（仅应用）

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
        
        //——— 相位切换判定：达到样本阈值则进入“仅应用/传播”模式 ———//
        if (!apply_only && (unsat_count >= NEED_UNSAT && sat_count >= NEED_SAT)) {
            apply_only = true;
            std::cout << "[Mode] Switch to Apply-Only.\n"; 
        }
        
        
        if(current->is_value()) {
            if(!apply_only){
                simulate_constant_node(current, num_iterations, node_data_map);
                substitution_map.insert_or_assign(current, current);
                hash_term_map[node_data_map[current].hash()].push_back(current);
            } else {
                substitution_map.insert_or_assign(current, current);
            }
            processed_nodes++;
            node_stack.pop();

            // progress tracking
            while (processed_nodes * 100 / total_nodes >= next_progress_milestone) {
                std::cout << "[Progress] " << next_progress_milestone
                          << "% (" << processed_nodes << "/" << total_nodes << " nodes processed)\n";
                next_progress_milestone += 10;
            }
            continue;
        }

        if(current->is_symbolic_const() && current->get_op().is_null()) {
            if (!apply_only) {
                simulate_leaf_node(current, num_iterations, node_data_map, dump_file_path, load_file_path);
                substitution_map.emplace(current, current);
            } else {
                substitution_map.emplace(current, current);
            }
            processed_nodes++;
            node_stack.pop();

            // progress tracking
            while (processed_nodes * 100 / total_nodes >= next_progress_milestone) {
                std::cout << "[Progress] " << next_progress_milestone
                          << "% (" << processed_nodes << "/" << total_nodes << " nodes processed)\n";
                next_progress_milestone += 10;
            }
            continue;
        }
         
        // 一般内部节点
        TermVec children(current->begin(), current->end());
        TermVec children_substituted;
        children_substitution(children, children_substituted, substitution_map);
        if (children_substituted.size() != children.size())
            throw std::runtime_error("children_substitution size mismatch");

        bool substitution_happened = false;
        for (size_t i = 0; i < children.size(); ++i) {
            if (children_substituted[i] != children[i]) { 
                substitution_happened = true; 
                break;
            }
        }
        
        // create a new term with the substituted children
        auto op_type = current->get_op();
        Term cnode = substitution_happened ? solver->make_term(op_type, children_substituted) : current;
        // 相位B：仅应用/传播（彻底跳过昂贵操作）
        if (apply_only) {
            substitution_map.emplace(current, cnode);  // 结构哈希会自动合并语法等价
            processed_nodes++;
            node_stack.pop();

            // progress tracking
            while (processed_nodes * 100 / total_nodes >= next_progress_milestone) {
                std::cout << "[Progress] " << next_progress_milestone
                          << "% (" << processed_nodes << "/" << total_nodes << " nodes processed)\n";
                next_progress_milestone += 10;
            }
            continue;
        }

        // —— 相位A：等价“发现”路径 —— //
        NodeData sim_data;
        compute_simulation(children_substituted, num_iterations, op_type, node_data_map, all_luts, sim_data);
        auto current_hash = sim_data.hash();
        Term term_eq = nullptr;

        auto ordering_start = std::chrono::high_resolution_clock::now();
        TryFindResult result = try_find_equiv_term(cnode, current_hash, sim_data,
                                                num_iterations, hash_term_map,
                                                node_data_map, substitution_map, debug);
        auto ordering_end = std::chrono::high_resolution_clock::now();
        auto ordering_duration = std::chrono::duration_cast<std::chrono::milliseconds>(ordering_end - ordering_start);
        auto ordering_elapsed = ordering_duration.count();
        ordering_time += ordering_duration;
        if (result.found && result.term_eq) { // term_eq is the same as cnode
            substitution_map.insert({current, result.term_eq});
        } else {
            for (const auto & t : result.terms_for_solving) {
                if (unsat_count >= NEED_UNSAT && sat_count >= NEED_SAT) break;
                solver->push();
                auto eq = solver->make_term(Equal, t, cnode);
                solver->assert_formula(solver->make_term(Not, eq));
                auto start = std::chrono::high_resolution_clock::now();
                auto res = solver->check_sat();
                auto end = std::chrono::high_resolution_clock::now();
                auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);
                auto elapsed = duration.count();
                count++;

                if (res.is_unsat()) {
                    total_unsat_time += duration;
                    unsat_count++;
                    term_eq = t;
                    substitution_map.insert({current, t});
                    solver->pop();
                    break;
                } else {
                    total_sat_time += duration;
                    sat_count++;
                    fill_simulation_data_for_all_nodes(node_data_map, solver, num_iterations, substitution_map,all_luts); //FIXME
                    solver->pop();
                }
            }
        }

        if (term_eq && term_eq != nullptr) {
            substitution_map.insert_or_assign(current, term_eq);
        } else {
            substitution_map.insert_or_assign(current, cnode);
            hash_term_map[current_hash].push_back(cnode);
            node_data_map[cnode] = std::move(sim_data);
        }
        processed_nodes++;   
        
        //progress tracking
        while (processed_nodes * 100 / total_nodes >= next_progress_milestone) {
            std::cout << "[Progress] " << next_progress_milestone << "% (" << processed_nodes << "/" << total_nodes << " nodes processed)\n";
            next_progress_milestone += 10;
        }

        node_stack.pop();
    }
}




} // namespace sweeper
