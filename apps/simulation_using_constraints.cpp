

//-----------------------------------------------
// | this is the simualtion function for the constraint-based simulation
// | here , input_terms contains free symbols 
// | this function can reduce the post order sat counts
//-----------------------------------------------



template <typename TermIterable>
void simulation_using_constraint(TermIterable & input_terms,
                int & num_iterations,
                std::unordered_map<Term, NodeData> & node_data_map,
                std::string & dump_file_path,
                std::string & load_file_path,
                SmtSolver &solver,
                double & success_rate,
                const smt::TermVec & constraints)          
{
    GmpRandStateGuard rand_guard;
    std::unordered_map<Term, std::string> constraint_input_map;
    match_term_constraint_pattern(constraints, constraint_input_map);

    //--------------load simulation input-----------------
    std::ofstream dumpfile;
    if (!load_file_path.empty()) {
        std::ifstream infile(load_file_path);
        if (!infile.is_open()) {
            std::cerr << "[ERROR] Cannot open simulation input file: " << load_file_path << std::endl;
            return;
        }

        std::unordered_map<std::string, Term> term_lookup;
        for (const auto & term : input_terms) {
            term_lookup[term->to_string()] = term;
        }

        std::string line;
        while (std::getline(infile, line)) {
            if (line.empty() || line[0] == '[') continue;
            size_t pos = line.find(" = ");
            if (pos == std::string::npos) continue;
            std::string term_str = line.substr(0, pos);
            std::string val_str = line.substr(pos + 3);
            
            auto it = term_lookup.find(term_str);
            if (it != term_lookup.end()) {
                auto bv_input = btor_bv_const(val_str.c_str(), it->second->get_sort()->get_width());
                node_data_map[it->second].get_simulation_data().push_back(std::move(bv_input));
            }
        }

        // Check if all input terms have simulation data
        for (const auto & term : input_terms) {
            if (node_data_map[term].get_simulation_data().empty()) {
                std::cerr << "[ERROR] Missing simulation data for input: " << term->to_string() << std::endl;
                throw std::runtime_error("Incomplete simulation input file.");
            }
        }

        return;
    }

    //-----------------dump simulation input------------------
    if (!dump_file_path.empty()) {
        dumpfile.open(dump_file_path, std::ios::app);
        if (!dumpfile.is_open()) {
            std::cerr << "[ERROR] Cannot open dump file: " << dump_file_path << std::endl;
            return;
        }
        dumpfile << "[BEGIN NEW SIMULATION BATCH]\n";
    }


    std::size_t total_trials   = 0;
    std::size_t success_count  = 0;
    std::chrono::duration<double> total_sat_time(0);
    std::chrono::duration<double> total_unsat_time(0);

    for(auto constraint : constraints){
        solver->assert_formula(constraint);
    }

    auto erase_core = [](smt::TermVec &v, const UnorderedTermSet &core) -> std::size_t {
        const auto old_sz = v.size();
        v.erase(std::remove_if(v.begin(), v.end(),
                               [&](const Term &t){ return core.find(t) != core.end(); }),
                v.end());
        return old_sz - v.size();
    };
    
    for (int i = 0; i < num_iterations;)
    {
        if (dumpfile.is_open()) dumpfile << "[SIMULATION ITERATION " << i << "]\n";

        //--------------------Generate or overwrite random input-------------------
        std::unordered_map<Term, std::string> input_cache; // store input values
        for (const auto & t : input_terms) // generate random input
        {
            std::string val;
             auto it_fix = constraint_input_map.find(t);
            if (it_fix != constraint_input_map.end()) {
                val = it_fix->second;                
            } else {
                const auto width = t->get_sort()->get_width();
                mpz_t mpz; 
                mpz_init(mpz);
                rand_guard.random_input(mpz, width);
                std::unique_ptr<char, void(*)(void*)> s(mpz_get_str(nullptr, 2, mpz), free);
                mpz_clear(mpz);
                val = s.get();
                if (val.size() < width) val.insert(0, width - val.size(), '0');
            }
            input_cache.emplace(t, std::move(val));
        }

         // ---------- Construct the current assumption collection ----------
        smt::TermVec assumptions;
        assumptions.reserve(input_terms.size());
        for (const auto &t : input_terms) {
            const std::string &v = input_cache[t];
            Term val_term = solver->make_term(v.c_str(), solver->make_sort(BV, t->get_sort()->get_width()), 2);
            assumptions.push_back(solver->make_term(smt::Equal, t, val_term));
        }

        const auto ts_start = std::chrono::high_resolution_clock::now();
        Result result = solver->check_sat_assuming(assumptions);
        ++total_trials;

        // ---------- 1) deal with UNSAT and erase unsat core ----------
        bool sat_now = result.is_sat();
        if (!sat_now) {
            auto unsat_start = std::chrono::high_resolution_clock::now();
            bool progress = true;
            std::size_t refine_cnt = 0;

            while (result.is_unsat() && progress ) {
                UnorderedTermSet core;
                solver->get_unsat_assumptions(core);

                progress = erase_core(assumptions, core) > 0;
                if (!progress || assumptions.empty()) break;

                result = solver->check_sat_assuming(assumptions);
            }
            sat_now = result.is_sat();
            total_unsat_time += std::chrono::high_resolution_clock::now() - unsat_start;
        }
        
        //---------------2) deal with SAT -----------------
        if (sat_now) {
            const auto ts_start_sat = std::chrono::high_resolution_clock::now();
            ++i;
            ++success_count;

            for (const auto &t : input_terms) {
                const std::string &v = input_cache[t];
                auto bv = btor_bv_const(v.c_str(), t->get_sort()->get_width());
                node_data_map[t].get_simulation_data().push_back(std::move(bv));

                if (dumpfile.is_open())
                    dumpfile << t->to_string() << " = " << v << '\n';
            }

            auto sat_end = std::chrono::high_resolution_clock::now();
            total_sat_time += sat_end - ts_start_sat;

            std::cout << "[SAT]  iteration " << i
                      << "   (" << std::chrono::duration<double>(sat_end - ts_start_sat).count()
                      << " s)\n";
        } else {
            std::cout << "[Simulation] UNSAT — iteration discarded\n";
        }

        if (dumpfile.is_open()) dumpfile << '\n';
    }

    std::cout << "[Summary] Total SAT time: " << total_sat_time.count() << " seconds.\n";
    std::cout << "[Summary] Total UNSAT time: " << total_unsat_time.count() << " seconds.\n";

    success_rate = total_trials ? static_cast<double>(success_count) / total_trials : 0.0;

    if (dumpfile.is_open()) {
        dumpfile << "[END SIMULATION BATCH]\n";
        std::cout << "[Simulation] Dump saved → " << dump_file_path << '\n';
    }
}