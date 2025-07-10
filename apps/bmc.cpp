#include "./sweeping.h"
#include <gflags/gflags.h>

int main(int argc, char* argv[]) {
    Config config;

    if (!parse_arguments(argc, argv, config)) {
        return EXIT_FAILURE;
    }

    // DEBUG
    if (config.debug) {
        std::cout << "==== DEBUG ====" << std::endl;
        std::cout << "BTOR2 File           : " << config.btor2_file << std::endl;
        std::cout << "Simulation Iterations: " << config.simulation_iterations << std::endl;
        std::cout << "Solver Timeout (ms)  : " << config.solver_timeout_ms << std::endl;
        std::cout << "Property Timeout (ms): " << config.property_check_timeout_ms << std::endl;
        std::cout << "Dump SMT Enabled     : " << (config.dump_smt ? "Yes" : "No") << std::endl;
        std::cout << "Debug Enabled        : " << (config.debug ? "Yes" : "No") << std::endl;
        std::cout << "===============" << std::endl;
    }

    //parameter
    std::string btor2_file = config.btor2_file;
    int num_iterations = config.simulation_iterations;
    bool dump_smt = config.dump_smt;
    int solver_timeout_ms = config.solver_timeout_ms;
    int property_check_timeout_ms = config.property_check_timeout_ms;
    bool debug = config.debug;
    int bound = config.bound;
    std::string dump_input_file = config.dump_input_file;
    std::string load_input_file = config.load_input_file;

    //logging solver
    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;
    SmtSolver solver = BitwuzlaSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // Loading and parsing BTOR2 files
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(btor2_file, sts);

    const auto& input_terms = btor_parser.inputsvec(); // all input here
    const auto& output_terms = btor_parser.get_output_terms(); // all output here
    const auto& idvec = btor_parser.idvec();

    SymbolicSimulator sim(sts, solver);
    const auto & propvec = sts.prop();
    if (propvec.empty()) {
        std::cout << "No property to check!" << std::endl;
        return 1;
    }

    auto prop = and_vec(propvec, solver);
    sim.init();
    sim.set_input({},{});

    // if (! check_prop(
    //     sim.interpret_state_expr_on_curr_frame(prop, false),
    //     sim.all_assumptions(),
    //     solver )) {
    //     std::cout << "[bmc] failed at init!" << std::endl;
    //     return 2;
    // }

    
    for (unsigned i = 1; i<=bound; ++i) {
        
        sim.sim_one_step();
        sim.set_input({},{});
    }

    TermVec cons = sim.all_assumptions(); // this is the constraint
    for(auto constraint : cons){
        solver->assert_formula(constraint);
    }
    
    // init for each bound
    std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
    std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
    std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
    std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table
    auto root = sim.interpret_state_expr_on_curr_frame(prop, false);
    //get free symbols
    smt::UnorderedTermSet combined_set(input_terms.begin(), input_terms.end());
    smt::UnorderedTermSet out;
    smt::get_free_symbols(root, out);
    combined_set.insert(out.begin(), out.end());
    smt::TermVec combined_terms(combined_set.begin(), combined_set.end());
    //init for array
    initialize_arrays({&sts}, all_luts, substitution_map, debug);
    // simulation(combined_terms, num_iterations, node_data_map, dump_input_file, load_input_file);
    double success_rate = 0.0;
    simulation_using_constraint(combined_terms, num_iterations, node_data_map, dump_input_file, load_input_file, solver, success_rate, cons);
    auto simualtion_time = std::chrono::high_resolution_clock::now();
    auto elapsed_simulation_time = std::chrono::duration_cast<std::chrono::milliseconds>(simualtion_time - program_start_time);
    std::cout << "[Simulation] " << elapsed_simulation_time.count() / 1000.0 << " s" << std::endl;
    for(auto i : input_terms){
        assert(node_data_map[i].get_simulation_data().size() == num_iterations);
        substitution_map.insert({i, i});
        hash_term_map[node_data_map[i].hash()].push_back(i);
    }
    
    int count = 0;
    int unsat_count = 0;
    int sat_count = 0;
    int total_nodes = 0;
    int total_nodes_after = 0;
    std::chrono::milliseconds total_sat_time(0);
    std::chrono::milliseconds total_unsat_time(0); 
        
    //end of init
    post_order(root, node_data_map, hash_term_map, substitution_map, all_luts, count, unsat_count, sat_count,solver, num_iterations,dump_smt, input_terms, property_check_timeout_ms, debug, dump_input_file,load_input_file, total_sat_time,  total_unsat_time);
    root = substitution_map.at(root);
    count_total_nodes(root, total_nodes_after);
    cout << "total nodes: " << total_nodes_after << endl;
    auto time_end = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(time_end - program_start_time);
    std::cout << "[Pre]: " << elapsed_time.count() / 1000.0 << " s" << std::endl;
    auto solving_time_start = std::chrono::high_resolution_clock::now();
    if (check_prop(
        root,
        sim.all_assumptions(),
        solver )) {
        auto solving_time_end = std::chrono::high_resolution_clock::now();
        auto solving_time = std::chrono::duration_cast<std::chrono::milliseconds>(solving_time_end -solving_time_start);
        std::cout << "[Solving]: " << solving_time.count() / 1000.0 << " s" << std::endl;
        std::cout << "[Result] bound " <<  bound << " passed." << std::endl;
        cout << "total: " << count << " , unsat: " << unsat_count << " , sat: " << sat_count << ",unsat_time: "<< total_unsat_time.count() << " ms, sat_time: " << total_sat_time.count() << " ms" <<endl;
    } else {
        std::cout << "[Result] failed at bound " << bound << std::endl;
        cout << "total: " << count << " , unsat: " << unsat_count << " , sat: " << sat_count << ",unsat_time: "<< total_unsat_time.count() << " ms , sat_time: " << total_sat_time.count() << " ms" <<endl;
        return 2;
    }
        
    node_data_map.clear();
    substitution_map.clear();
    hash_term_map.clear();

    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;
    gflags::ShutDownCommandLineFlags();

    return 0;
}

