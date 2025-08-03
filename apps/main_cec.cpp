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
using namespace wasim;

int main(int argc, char* argv[])
{
    silence_cout();
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
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(config.btor2_file, sts, "a::");

    restore_cout();

    const auto& input_terms = btor_parser.inputsvec();

    std::unordered_map<smt::Term, NodeData> node_data_map;
    std::unordered_map<uint32_t, smt::TermVec> hash_term_map;
    std::unordered_map<smt::Term, smt::Term> substitution_map;
    std::unordered_map<smt::Term, std::unordered_map<std::string, std::string>> all_luts;

    // 数组初始化与等价替换
    initialize_arrays({&sts}, all_luts, substitution_map, config.debug);

    auto inputs_set = sts.inputvars();
    TermVec inputs(inputs_set.begin(), inputs_set.end());
    
    // Extract just the Term part from constraints
    TermVec constraints;
    for (const auto& constraint_pair : sts.constraints()) {
        constraints.push_back(constraint_pair.first);
    }
    
    auto property = sts.prop();

    // Simulation：为输入生成 num_iterations 批量样本；dump/load 可选
    simulation(inputs, config.simulation_iterations, node_data_map, config.dump_input_file, config.load_input_file, constraints);

    // 将输入纳入哈希桶并标记“已替代为自身”
    for (auto i : inputs) {
        if (node_data_map[i].get_simulation_data().size() != static_cast<size_t>(config.simulation_iterations))
            throw std::runtime_error("Input simulation size mismatch for " + i->to_string());
        substitution_map.insert({i, i});
        hash_term_map[node_data_map[i].hash()].push_back(i);
    }

    solver->assert_formula(sts.init());
    for (const auto & c : constraints) {
        solver->assert_formula(c);
    }

    int i = 0, total_nodes = 0;
    int count = 0, unsat_count = 0, sat_count = 0;
    std::chrono::milliseconds total_sat_time(0), total_unsat_time(0), ordering_time(0);

    for (auto root : property) {
        
        count_total_nodes(root, total_nodes);
        std::cout << "Total nodes : " << total_nodes << std::endl;

        pre_collect_constants({root}, node_data_map, hash_term_map, substitution_map, config.simulation_iterations);
        post_order(root, node_data_map, hash_term_map, substitution_map, all_luts,
                   count, unsat_count, sat_count, solver, config.simulation_iterations, config.dump_smt,
                   config.property_check_timeout_ms, config.debug,
                   config.dump_input_file, config.load_input_file,
                   total_sat_time, total_unsat_time, ordering_time);

        root = substitution_map.at(root);
        solver->push();
        solver->assert_formula(solver->make_term(smt::Not, root));
        auto solving_start = std::chrono::high_resolution_clock::now();
        auto res = solver->check_sat();
        auto solving_end  = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(solving_end - solving_start).count();
        solver->pop();
        auto pre_time = std::chrono::duration_cast<std::chrono::milliseconds>(solving_start - program_start_time).count();

        std::cout << "[Pre-processing] " << pre_time << " ms\n";
        std::cout << "[Solving] " << duration << " ms\n";

        if (res.is_unsat())      std::cout << "[RESULT] UNSAT\n";
        else if (res.is_sat())   std::cout << "[RESULT] SAT\n";
        else                     std::cout << "UNKNOWN - likely timed out\n";

        std::cout << "[Sweeping] " << count
            << ", [UNSAT] " << unsat_count << " ("
            << total_unsat_time.count()/1000.0 << " s), "
            << "[SAT] " << sat_count << " ("
            << total_sat_time.count()/1000.0 << " s)\n";

        ++i;
    }

    std::cout << "All property done\n";
    return EXIT_SUCCESS;
}