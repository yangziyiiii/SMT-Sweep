#include "sweeper/config.hpp"
#include "sweeper/simulation_engine.hpp"
#include "sweeper/node_data.hpp"
#include "sweeper/sweeper_engine.hpp"

#include "smt-switch/bitwuzla_factory.h"
#include "frontend/btor2_encoder.h"
#include "framework/ts.h"
#include "framework/symsim.h"

#include <fstream>
#include <iostream>
#include <filesystem>

using namespace sweeper;
using namespace wasim;

inline bool check_bmc_result(const smt::Term & prop,
                             const smt::TermVec & assumptions,
                             smt::SmtSolver & solver,
                             bool dump_enable,
                             const std::string & base_file_name,
                             int bound,
                             int & solve_time_ms
) {
    solver->push();
    for (const auto & a : assumptions) {
        solver->assert_formula(a);
    }
    solver->assert_formula(solver->make_term(smt::Not, prop));

    auto start = std::chrono::high_resolution_clock::now();
    auto res = solver->check_sat();
    auto end = std::chrono::high_resolution_clock::now();
    solve_time_ms = std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count();
    solver->pop();

    if (res.is_unsat()) return true;
    if (res.is_sat()) return false;
    throw std::runtime_error("[check_bmc_result] UNKNOWN result from solver.");
}

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
                  << "Bound                : " << config.bound << "\n"
                  << "Dump SMT Enabled     : " << (config.dump_smt ? "Yes" : "No") << "\n"
                  << "Debug Enabled        : " << (config.debug ? "Yes" : "No") << "\n";
    }

    auto program_start = std::chrono::high_resolution_clock::now();
    sweeper::last_time_point = program_start;

    smt::SmtSolver solver = smt::BitwuzlaSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    TransitionSystem sts(solver);
    BTOR2Encoder encoder(config.btor2_file, sts);
    SymbolicSimulator sim(sts, solver);

    restore_cout();

    const auto & propvec = sts.prop();
    if (propvec.empty()) {
        std::cerr << "[ERROR] No property found.\n";
        return EXIT_FAILURE;
    }

    auto prop = and_vec(propvec, solver);
    sim.init();
    sim.set_input({}, {});
    for (int i = 1; i <= config.bound; ++i) {
        sim.sim_one_step();
        sim.set_input({}, {});
    }

    auto root = sim.interpret_state_expr_on_curr_frame(prop, false);
    TermVec constraints = sim.all_assumptions();
    for (const auto & c : constraints) {
        solver->assert_formula(c);
    }

    std::unordered_map<smt::Term, NodeData> node_data_map;
    std::unordered_map<uint32_t, smt::TermVec> hash_term_map;
    std::unordered_map<smt::Term, smt::Term> substitution_map;
    std::unordered_map<smt::Term, std::unordered_map<std::string, std::string>> all_luts;

    smt::UnorderedTermSet free_symbols;
    smt::get_free_symbols(root, free_symbols);
    std::cout << "[INPUT] Free symbols: " << free_symbols.size() << "\n";

    std::chrono::milliseconds total_sat_time(0);
    std::chrono::milliseconds total_unsat_time(0);

    auto pre_done = std::chrono::high_resolution_clock::now();
    auto pre_time = std::chrono::duration_cast<std::chrono::milliseconds>(pre_done - program_start).count();
    std::cout << "[Pre-processing] " << pre_time/1000.0 << " s\n";

    int solve_time_ms = 0;
    auto solving_start = std::chrono::high_resolution_clock::now();

    solver->push();
    solver->assert_formula(solver->make_term(smt::Not, root));
    auto res = solver->check_sat();
    solver->pop();

    auto solving_end = std::chrono::high_resolution_clock::now();
    solve_time_ms = std::chrono::duration_cast<std::chrono::milliseconds>(solving_end - solving_start).count();
    std::cout << "[Solving] " << solve_time_ms/1000.0 << " s\n";

    if (res.is_unsat()) {
        total_unsat_time += std::chrono::milliseconds(solve_time_ms);
        std::cout << "[RESULT] Bound " << config.bound << " passed."<<std::flush;
    } else if (res.is_sat()) {
        total_sat_time += std::chrono::milliseconds(solve_time_ms);
        std::cout << "[RESULT] Failed at bound " << config.bound << std::flush;
    } else {
        std::cerr << "[ERROR] Solver returned UNKNOWN.\n";
    }



    auto program_end = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end - program_start).count();
    std::cout << "[Total Execution] " << total_time/1000.0 << " s\n";
    return EXIT_SUCCESS;
}
