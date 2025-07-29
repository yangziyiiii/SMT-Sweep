#include "./sweeping.h"

#define SWEEPING_UTILS_H

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
    solver->set_opt("time-limit", std::to_string(property_check_timeout_ms / 1000.0));  // set time limit

    // Loading and parsing BTOR2 files
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(btor2_file, sts, "a::");

    std::cout << "============================" << std::endl;

    // cout << "Loading and parsing BTOR2 files..." << endl;

    const auto& input_terms = btor_parser.inputsvec(); // all input here
    const auto& output_terms = btor_parser.get_output_terms(); // all output here
    const auto& constraints = btor_parser.get_const_terms(); // all constraints here
    const auto& property = btor_parser.propvec(); // all properties here
    const auto& idvec = btor_parser.idvec();

    // cout << "Constraints: " << constraints.size() << endl;
    for(auto c : constraints) {
        solver->assert_formula(c);
    }

    std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
    std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
    std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
    std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table

    std::cout << "stage 1 : init array & simualtion ... ";

    //Array init
    initialize_arrays({&sts}, all_luts, substitution_map, debug);

    std::cout << ">> Dump Path = " << dump_input_file << std::endl;
    std::cout << ">> Load Path = " << load_input_file << std::endl;
    //simulation
    // simulation(input_terms, num_iterations, node_data_map, dump_input_file, load_input_file, constraints);
    double success_rate = 0.0;
    simulation_using_constraint(input_terms, num_iterations, node_data_map, dump_input_file, load_input_file, solver, success_rate, constraints);
    std::cout << "done" <<std::endl;
    //end of simulation

    solver->assert_formula(sts.init());
    for (const auto & c : sts.constraints()) solver->assert_formula(c.first);
    
    //start post order traversal
    int count = 0;
    int unsat_count = 0;
    int sat_count = 0;
    int i = 0;
    std::chrono::milliseconds total_sat_time(0);
    std::chrono::milliseconds total_unsat_time(0);

    std::cout << "============================" << std::endl;
    std::cout << "stage 2 : begin sweeping ... " << std::endl;
    

    //Add constraint into root
    std::vector<Term> traversal_roots; 
    traversal_roots.push_back(sts.init());
    for(auto constraint_pair : sts.constraints()) {
        traversal_roots.push_back(constraint_pair.first);
    }

    cout << "Property size: " << property.size() << endl;
    for(auto root : property) {
        
        traversal_roots.push_back(root);
        pre_collect_constants(traversal_roots, node_data_map, hash_term_map, substitution_map, num_iterations);
        std::cout << "pre_collect_constants done" << std::endl;
        std::set<Term> unique_roots(traversal_roots.begin(), traversal_roots.end());
        std::vector<Term> final_roots(unique_roots.begin(), unique_roots.end());

        Term combined_term = solver->make_term(And, final_roots);
        // post_order(combined_term, node_data_map, hash_term_map, substitution_map, all_luts, count, unsat_count, sat_count, solver, num_iterations, dump_smt, input_terms, property_check_timeout_ms, debug, dump_input_file, load_input_file, total_sat_time, total_unsat_time);
        print_time();

        // root = substitution_map.at(root);
        int total_nodes = 0;
        count_total_nodes(root, total_nodes);
        cout << "total nodes: " << total_nodes << endl;

        cout << "Property ID: " << idvec[i] << " ";
        solver->push();
        auto not_root = solver->make_term(Not, root);
        solver->assert_formula(not_root);
        
        // Continue with the original solver for checking satisfiability
        auto start_time = std::chrono::high_resolution_clock::now();
        auto res = solver->check_sat();
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
        
        solver->pop();

        if(res.is_unsat()){
            std::cout << "Result : UNSAT (took " << duration << "ms)" << std::endl;
        } else if(res.is_sat()) {
            std::cout << "Result : SAT (took " << duration << "ms)" << std::endl;
        } else {
            std::cout << "Result : UNKNOWN - likely timed out after " << duration << "ms" << std::endl;
        }

        std::cout << "for this property, " << unsat_count << " UNSAT when merging, using " << total_unsat_time.count()/1000 << " s and " << sat_count << " SAT when merging, using " << total_sat_time.count()/1000 << " s" << std::endl;
        cout << "-----------------" << endl;

        i++;
    }

    std::cout << "All property done" << std:: endl;
    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;
    std::cout << "============================" << std::endl;

    return 0;
}
