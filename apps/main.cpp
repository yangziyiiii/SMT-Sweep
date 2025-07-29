#include "sweeper/config.hpp"
#include "sweeper/simulation_engine.hpp"
#include "sweeper/node_data.hpp"
#include "sweeper/sweeper_engine.hpp"

#include "smt-switch/bitwuzla_factory.h"
#include "frontend/btor2_encoder.h"
#include "framework/ts.h"

#include <set>
#include <iostream>

using namespace sweeper;

int run(int argc, char* argv[])
{
    Config config;
    if (!parse_arguments(argc, argv, config)) return EXIT_FAILURE;

    if (config.debug) {
        std::cout << "==== DEBUG ====\n"
                  << "BTOR2 File           : " << config.btor2_file << "\n"
                  << "Simulation Iterations: " << config.simulation_iterations << "\n"
                  << "Solver Timeout (ms)  : " << config.solver_timeout_ms << "\n"
                  << "Property Timeout (ms): " << config.property_check_timeout_ms << "\n"
                  << "Dump SMT Enabled     : " << (config.dump_smt ? "Yes" : "No") << "\n"
                  << "Debug Enabled        : " << (config.debug ? "Yes" : "No") << "\n";
    }

    auto program_start_time = std::chrono::high_resolution_clock::now();
    sweeper::last_time_point = program_start_time;

    smt::SmtSolver solver = smt::BitwuzlaSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // 解析 BTOR2
    wasim::TransitionSystem sts(solver);
    wasim::BTOR2Encoder btor_parser(config.btor2_file, sts);

    const auto& input_terms = btor_parser.inputsvec();
    const auto& constraints = btor_parser.get_const_terms();
    const auto& property    = btor_parser.propvec();
    const auto& idvec       = btor_parser.idvec();

    std::cout << "============================\n";
    std::cout << "Constraints: " << constraints.size() << "\n"
              << "input: "      << input_terms.size()  << "\n"
              << "Property size: " << property.size()   << "\n";

    std::unordered_map<smt::Term, NodeData> node_data_map;
    std::unordered_map<uint32_t, smt::TermVec> hash_term_map;
    std::unordered_map<smt::Term, smt::Term> substitution_map;
    std::unordered_map<smt::Term, std::unordered_map<std::string, std::string>> all_luts;

    // 数组初始化与等价替换
    initialize_arrays({&sts}, all_luts, substitution_map, config.debug);

    // 收集 property 的自由符号，剔除数组
    smt::UnorderedTermSet free_symbols;
    smt::get_free_symbols(property.at(0), free_symbols);
    smt::UnorderedTermSet to_remove;
    for (auto i : free_symbols)
        if (i->get_sort()->get_sort_kind() == smt::ARRAY)
            to_remove.insert(i);
    for (auto i : to_remove) free_symbols.erase(i);

    // Simulation：为输入生成 num_iterations 批量样本；dump/load 可选
    simulation(free_symbols, config.simulation_iterations,
               node_data_map, config.dump_input_file, config.load_input_file, constraints);

    // 将输入纳入哈希桶并标记“已替代为自身”
    for (auto i : free_symbols) {
        if (node_data_map[i].get_simulation_data().size() != static_cast<size_t>(config.simulation_iterations))
            throw std::runtime_error("Input simulation size mismatch for " + i->to_string());
        substitution_map.insert({i, i});
        hash_term_map[node_data_map[i].hash()].push_back(i);
    }

    std::cout << "Simulation done.\n";

    solver->assert_formula(sts.init());
    for (const auto & c : sts.constraints()) solver->assert_formula(c.first);

    int i = 0;
    int count = 0, unsat_count = 0, sat_count = 0;
    std::chrono::milliseconds total_sat_time(0), total_unsat_time(0);

    std::cout << "============================\n";
    std::cout << "stage 2 : begin sweeping ... \n";

    std::vector<smt::Term> traversal_roots;
    traversal_roots.push_back(sts.init());
    for (auto & cp : sts.constraints()) traversal_roots.push_back(cp.first);

    smt::UnorderedTermSet out;
    for (auto root : property) {
        traversal_roots.push_back(root);
        pre_collect_constants(traversal_roots, node_data_map, hash_term_map, substitution_map, config.simulation_iterations);

        std::set<smt::Term> unique_roots(traversal_roots.begin(), traversal_roots.end());
        std::vector<smt::Term> final_roots(unique_roots.begin(), unique_roots.end());
        smt::Term combined = sweeper::and_vec(final_roots, solver);

        post_order(combined, node_data_map, hash_term_map, substitution_map, all_luts,
                   count, unsat_count, sat_count, solver, config.simulation_iterations, config.dump_smt,
                   input_terms, config.property_check_timeout_ms, config.debug,
                   config.dump_input_file, config.load_input_file,
                   total_sat_time, total_unsat_time, out);
        sweeper::print_time();

        // 用替换后的 root 做最终验证
        root = substitution_map.at(root);
        int total_nodes = 0; count_total_nodes(root, total_nodes);
        std::cout << "total nodes: " << total_nodes << "\n";

        std::cout << "Property ID: " << idvec[i] << " ";
        solver->push();
        solver->assert_formula(solver->make_term(smt::Not, root));
        auto start = std::chrono::high_resolution_clock::now();
        auto res = solver->check_sat();
        auto end  = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
        solver->pop();

        if (res.is_unsat())      std::cout << "Result : UNSAT (took " << duration << "ms)\n";
        else if (res.is_sat())   std::cout << "Result : SAT (took " << duration << "ms)\n";
        else                     std::cout << "Result : UNKNOWN - likely timed out after " << duration << "ms\n";

        std::cout << "for this property, " << unsat_count << " UNSAT when merging, using "
                  << total_unsat_time.count()/1000 << " s and " << sat_count
                  << " SAT when merging, using " << total_sat_time.count()/1000 << " s\n";
        std::cout << "-----------------\n";
        ++i;
    }

    std::cout << "All property done\n";
    return EXIT_SUCCESS;
}

int main(int argc, char* argv[])
{
    return run(argc, argv);
}
