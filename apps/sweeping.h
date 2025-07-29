#include "node_data.h"


template <typename TermIterable>
void load_simulation_input(const std::string & path,
                           const TermIterable & input_terms,
                           std::unordered_map<Term, NodeData> & node_data_map)
{
    std::ifstream infile(path);
    if (!infile.is_open()) {
        std::cerr << "[ERROR] Cannot open simulation input file: " << path << std::endl;
        return;
    }

    std::string line;
    while (std::getline(infile, line)) {
        if (line.empty() || line[0] == '[') continue;
        size_t pos = line.find(" = ");
        if (pos == std::string::npos) continue;
        std::string term_str = line.substr(0, pos);
        std::string val_str = line.substr(pos + 3);
        for (const auto & term : input_terms) {
            if (term->to_string() == term_str) {
                auto bv_input = btor_bv_const(val_str.c_str(), term->get_sort()->get_width());
                node_data_map[term].get_simulation_data().push_back(btor_bv_const(val_str.c_str(), term->get_sort()->get_width()));
            }
        }
    }
}

std::string apply_extract_constraint(const std::string & base_value, int high, int low, const std::string & extract_value)
{
    std::string result = base_value;
    int total_width = base_value.size();
    int extract_width = high - low + 1;
    std::string padded_extract = extract_value;
    if (extract_value.size() < static_cast<size_t>(extract_width)) {
        padded_extract = std::string(extract_width - extract_value.size(), '0') + extract_value;
    }
    for (int i = 0; i < extract_width; ++i) {
        int pos = total_width - 1 - low - i;
        if (pos >= 0 && pos < total_width)
            result[pos] = padded_extract[extract_width - 1 - i];
    }
    return result;
}





template <typename TermIterable>
void simulation(const TermIterable & input_terms,
                int num_iterations,
                std::unordered_map<Term, NodeData> & node_data_map,
                std::string & dump_file_path,
                std::string & load_file_path,
                const smt::TermVec & constraints = {})          
{
    GmpRandStateGuard rand_guard;
    std::unordered_map<Term, std::string> constraint_input_map;
    match_term_constraint_pattern(constraints, constraint_input_map);

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
                node_data_map[it->second].get_simulation_data().push_back(btor_bv_const(val_str.c_str(), it->second->get_sort()->get_width()));
            }
        }
        std::cout << "[Simulation] Loaded input simulation values from: " << load_file_path << std::endl;
        return;
    }

    if (!dump_file_path.empty()) {
        dumpfile.open(dump_file_path, std::ios::app);
        if (!dumpfile.is_open()) {
            std::cerr << "[ERROR] Cannot open dump file: " << dump_file_path << std::endl;
            return;
        }
        dumpfile << "[BEGIN NEW SIMULATION BATCH]\n";
    }

    for (int i = 0; i < num_iterations; ++i)
    {
        if (dumpfile.is_open()) dumpfile << "[SIMULATION ITERATION " << i << "]\n";
        for (const auto & term : input_terms)
        {
            std::string value_str;
            if (constraint_input_map.find(term) != constraint_input_map.end()) {
                value_str = constraint_input_map[term];
                if (value_str.rfind("EXTRACT_", 0) == 0) {
                    std::string base(term->get_sort()->get_width(), '0');
                    size_t eq_pos = value_str.find('=');
                    std::string tag = value_str.substr(0, eq_pos);
                    std::string extract_val = value_str.substr(eq_pos + 1);
                    size_t hpos = tag.find('_', 8);
                    int high = std::stoi(tag.substr(8, hpos - 8));
                    int low = std::stoi(tag.substr(hpos + 1));
                    value_str = apply_extract_constraint(base, high, low, extract_val);
                }
            }
            else {
                const auto width = term->get_sort()->get_width();
                mpz_t input_mpz;
                rand_guard.random_input(input_mpz, width);
                std::unique_ptr<char, void (*)(void *)> input_str(
                    mpz_get_str(nullptr, 2, input_mpz), free);
                mpz_clear(input_mpz);
                value_str = input_str.get();
            }

            if (value_str.size() < term->get_sort()->get_width()) {
                size_t pad_len = term->get_sort()->get_width() - value_str.size();
                value_str = std::string(pad_len, '0') + value_str;
            }

            auto bv_input = btor_bv_const(value_str.c_str(), term->get_sort()->get_width());
            node_data_map[term].get_simulation_data().push_back(btor_bv_const(value_str.c_str(), term->get_sort()->get_width()));
            if (dumpfile.is_open()) dumpfile << term->to_string() << " = " << value_str << "\n";
        }
        if (dumpfile.is_open()) dumpfile << "\n";
    }

    if (dumpfile.is_open()) {
        dumpfile << "[END SIMULATION BATCH]\n";
        dumpfile.close();
        std::cout << "[Simulation] Dumped input simulation values to: " << dump_file_path << std::endl;
    }
}


template <typename TermIterable>
smt::TermVec random_simulation(
    const TermIterable & inputs,
    const smt::SmtSolver & solver,
    GmpRandStateGuard & rand_guard,
    unordered_map<Term,string> & val_out
){
    TermVec assumptions;
    assumptions.reserve(inputs.size());

    for (const Term & in : inputs){
        Sort s = in->get_sort();
        switch (s->get_sort_kind()) {
            case BV: {
                // For bit-vector sorts, we generate a random bit-vector
                int width = s->get_width();
                mpz_t input_mpz;
                rand_guard.random_input(input_mpz, width);
                std::unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(nullptr, 2, input_mpz), free);
                mpz_clear(input_mpz);
                val_out[in] = std::string(input_str.get());
                Sort bv_sort = solver->make_sort(BV, width);
                Term input_random_val = solver->make_term(string(input_str.get()), bv_sort, 2);
                assert(input_random_val->get_sort()->get_width() == width);
                Term eq = solver->make_term(Equal, in, input_random_val);
                // std::cout << in->to_string() << ": " << input_random_val << std::endl;
                assumptions.push_back(eq);
                break;
            }
            case BOOL: {
                // For boolean sorts, we randomly choose true or false
                bool value = rand() % 2;
                Term input_random_val = solver->make_term(value ? 1 : 0);
                Term eq = solver->make_term(Equal, in, input_random_val);
                // std::cout << in->to_string() << ": " << input_random_val << std::endl;
                assumptions.push_back(eq);
                val_out[in] = value ? "1" : "0";
                break;
            }
            default:
                throw SmtException("Unsupported sort for random simulation: " + s->to_string());
        }    
    }

    return assumptions;
}


// TODO
//在第一次生成之后，有两个优化的点
//一个是对于unsat core的部分直接random (这个应该速度就比较快)
//另一个是对于sat 的部分重新random，然后在reduce unsat core （这个应该耗时会很久，但是应该会提升coverage）
std::string ensure_width(const std::string & val, uint64_t width) {
        if (val.size() < width) {
            return std::string(width - val.size(), '0') + val;
        } else if (val.size() > width) {
            return val.substr(val.size() - width);  // 截断高位保留低位
        } else {
            return val;
        }
    }


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
    // match_term_constraint_pattern(constraints, constraint_input_map); //TODO

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



    for(auto constraint : constraints){
        solver->assert_formula(constraint);
    }
    
    int total_trials = 0;
    int success_count = 0;

    

    while(success_count < num_iterations) {
        solver->push();
        ++total_trials;
        if (dumpfile.is_open()) dumpfile << "[SIMULATION ITERATION " << total_trials << "]\n";

        TermVec input_cache;
        TermVec reduce_cache;
        unordered_map<Term, string> rand_val; //for each bound
        unordered_map<Term, string> reduce_val; //for each bound
        TermVec assumptions;

        if(!input_cache.empty()){
            assumptions = random_simulation(input_cache, solver, rand_guard, rand_val);
        }else {
            assumptions = random_simulation(input_terms, solver, rand_guard, rand_val);
        }

        Result result = solver->check_sat_assuming(assumptions);
        

        if (result.is_sat()) {
            success_count++;
            std::cout << "[Simulation] Trial " << success_count << " is SAT." << std::endl;
            
            for (const auto & it : input_terms) {
                std::string vstr;
                if (auto it_rand = rand_val.find(it); it_rand != rand_val.end())
                    vstr = it_rand->second;
                else if (auto it_reduce = reduce_val.find(it); it_reduce != reduce_val.end())
                    vstr = it_reduce->second;
                else {
                    Term mval = solver->get_value(it);
                    vstr = mval->to_string();
                }

                uint64_t width = it->get_sort()->get_width();
                vstr = ensure_width(vstr, width);

                node_data_map[it].get_simulation_data().push_back(
                    btor_bv_const(vstr.c_str(), it->get_sort()->get_width()));

                if (dumpfile.is_open())
                    dumpfile << it->to_string() << " = " << vstr << '\n';
            }
        } else if(result.is_unsat()) {
            UnorderedTermSet core;
            solver->get_unsat_assumptions(core);
            std::cout << "[Reduce 1] core size, before " << core.size() ;
            reduce_unsat_core_to_fixedpoint(core, solver, result);
            std::cout << ", after " << core.size() << std::endl;
            TermList corelist(core.begin(), core.end());
            std::cout << "[Reduce] after reduce core: " << core.size() << std::endl;
            auto term_to_reduce = get_first_unreducible_term(corelist, solver, result);

            // for(auto term_to_reduce : core) {
                assumptions.erase(remove_if(assumptions.begin(), assumptions.end(),
                          [&](const Term & t) { return t == term_to_reduce; }),assumptions.end());
                TermVec children(term_to_reduce->begin(), term_to_reduce->end());
                reduce_val.insert({children[0], rand_val[children[0]]});
            // }

            while(!assumptions.empty()) {
                Result r = solver->check_sat_assuming(assumptions);
                if (r.is_sat()) {
                    success_count++;
                    std::cout << "[Simulation] Trial " << success_count << " is SAT after reducing assumptions." << std::endl;
                    for (const auto & term : input_terms) {
                        //find term from assumptions
                        for(auto assump : assumptions) {
                            TermVec children(assump->begin(), assump->end());
                            if( children[0] == term) {
                                auto val_here = children[1]->to_string();
                                uint64_t width = term->get_sort()->get_width();
                                val_here = ensure_width(val_here, width);
                                node_data_map[term].get_simulation_data().push_back(
                                    btor_bv_const(val_here.c_str(), term->get_sort()->get_width()));
                                if (dumpfile.is_open())
                                    dumpfile << term->to_string() << " = " << val_here << '\n';
                            } else {
                                Term mval = solver->get_value(term);
                                std::string vstr = mval->to_string();
                                uint64_t width = term->get_sort()->get_width();
                                vstr = ensure_width(vstr, width);
                                node_data_map[term].get_simulation_data().push_back(
                                    btor_bv_const(vstr.c_str(), term->get_sort()->get_width()));
                                if (dumpfile.is_open())
                                    dumpfile << term->to_string() << " = " << vstr << '\n';
                            }
                                
                        }
                    }
                    break; 
                }else {
                    UnorderedTermSet core;
                    solver->get_unsat_assumptions(core);
                    std::cout << "[Reduce 2] core size, before " << core.size();
                    reduce_unsat_core_to_fixedpoint(core, solver, r);
                    std::cout << ", after " << core.size() << std::endl;
                    TermList corelist(core.begin(), core.end());
                    auto term_to_reduce = get_first_unreducible_term(corelist, solver, r);
                    // for(auto term_to_reduce : core) {
                        assumptions.erase(remove_if(assumptions.begin(), assumptions.end(),
                                [&](const Term & t) { return t == term_to_reduce; }),assumptions.end());
                        TermVec children(term_to_reduce->begin(), term_to_reduce->end());
                        reduce_val.insert({children[0], rand_val[children[0]]});
                    // }
                }
                
            }
        }

        solver->pop();
        if (dumpfile.is_open()) dumpfile << '\n';
    }



    if (dumpfile.is_open()) {
        dumpfile << "[END SIMULATION BATCH]\n";
        std::cout << "[Simulation] Dump saved → " << dump_file_path << '\n';
    }
}



void simulate_leaf_node(const smt::Term& current, 
                        int & num_iterations, 
                        std::unordered_map<Term, NodeData>& node_data_map,
                        std::string & dump_file_path,
                        std::string & load_file_path) {
    if (has_simulation_data(current, node_data_map)) return;
    simulation(TermVec{current}, num_iterations, node_data_map, dump_file_path, load_file_path);
    assert(node_data_map[current].get_simulation_data().size() == num_iterations);
}



void post_order(smt::Term& root,
                std::unordered_map<Term, NodeData>& node_data_map,
                std::unordered_map<uint32_t, TermVec>& hash_term_map,
                std::unordered_map<Term, Term>& substitution_map,
                const std::unordered_map<Term, std::unordered_map<std::string, std::string>> & all_luts,
                int& count,
                int& unsat_count,
                int& sat_count,
                SmtSolver& solver,
                int& num_iterations,
                bool & dump_enable,
                const TermVec & input_terms,
                int & timeout_ms,
                bool & debug,
                std::string & dump_file_path,
                std::string & load_file_path,
                std::chrono::milliseconds& total_sat_time,
                std::chrono::milliseconds& total_unsat_time,
                smt::UnorderedTermSet & free_symbols)
{
    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});
    
    // Variables for progress tracking
    int total_nodes = 0;
    int processed_nodes = 0;
    enum SweepingStep { NONE, SUBST_CHECK, LEAF_NODE, CONST_NODE, SIM_NODE, MAP_UPDATE, FIND_CHILD, EQUIV_CHECK, RESULT_SAT  };
    SweepingStep current_step = NONE;
    std::string step_names[] = {
        "IDLE",
        "SUBST CHECK",
        "LEAF NODE",
        "CONST NODE",
        "SIM NODE",
        "MAP UPDATE",
        "FIND CHILD",
        "EQUIV CHECK",
        "RESULT SAT"
    };

    // First pass to count total nodes (optional but gives more accurate progress)
    count_total_nodes(root, total_nodes);
    std::cout << "Begin sweeping with " << total_nodes << " nodes..." << std::endl;

    // Function to update and display progress
    // auto //update_progress = [&](SweepingStep step) {
    //     current_step = step;
    //     const int bar_width = 50;
    //     float progress = (float)processed_nodes / total_nodes;
        
    //     std::cout << "\r[";
    //     int pos = bar_width * progress;
    //     for (int i = 0; i < bar_width; ++i) {
    //         if (i < pos) std::cout << "=";
    //         else if (i == pos) std::cout << ">";
    //         else std::cout << " ";
    //     }
    //     std::cout << "] " << int(progress * 100.0) << "% | "
    //               << "Step: " << step_names[step] << " | "
    //               << processed_nodes << "/" << total_nodes << " nodes"
    //               << std::flush;
    // };

    while(!node_stack.empty()) {
        auto & [current,visited] = node_stack.top();
        if(substitution_map.find(current) != substitution_map.end()) {
            node_stack.pop();
            continue;
        }

        if(!visited) {
            // push all children onto stack
            for(Term child : current) {
                if(child->get_sort()->get_sort_kind() == BV || child->get_sort()->get_sort_kind() == BOOL) {
                    node_stack.push({child,false});
                }
            }
            visited = true;
        } else {
            TermVec children(current->begin(), current->end());

            if(current->is_value()) { // constant
                //update_progress(CONST_NODE);
                simulate_constant_node(current, num_iterations, node_data_map);
                substitution_map.insert({current, current});
                hash_term_map[node_data_map[current].hash()].push_back(current);
                processed_nodes++;
            } 

            else if(current->is_symbolic_const() && current->get_op().is_null()) { // leaf nodes
                //update_progress(LEAF_NODE);
                assert(TermVec(current->begin(), current->end()).empty());// no children
                assert(current->get_sort()->get_sort_kind() != ARRAY); // no array
                simulate_leaf_node(current, num_iterations, node_data_map, dump_file_path, load_file_path);
                substitution_map.insert({current, current}); 
                processed_nodes++;
            }
            
            else { // compute simulation data for current node
                TermVec children(current->begin(), current->end()); // find children
                auto child_size = children.size();

                //update_progress(FIND_CHILD);
                bool substitution_happened = false;
                TermVec children_substituted;
                children_substitution(children, children_substituted, substitution_map);
                assert(children_substituted.size() == child_size);
                for (size_t i = 0; i < child_size; ++ i){
                    if (children_substituted.at(i) != children.at(i)) {
                        substitution_happened = true;
                        break;
                    }
                }
                
                auto op_type = current->get_op();
                Term cnode = substitution_happened ? solver->make_term(op_type, children_substituted) : current;

                NodeData sim_data;
                Term term_eq = nullptr; 
                compute_simulation(children_substituted, num_iterations, op_type, node_data_map, all_luts, sim_data);           
                auto current_hash = sim_data.hash();

                // update_progress(EQUIV_CHECK);
                TryFindResult result = try_find_equiv_term(cnode, 
                                                           current_hash, 
                                                           sim_data, 
                                                           num_iterations, 
                                                           hash_term_map, 
                                                           node_data_map, 
                                                           substitution_map, 
                                                           debug);
                // TryFindResult result = try_find_equiv_term_heur(cnode, 
                //                                            current_hash, 
                //                                            sim_data, 
                //                                            num_iterations, 
                //                                            hash_term_map, 
                //                                            node_data_map, 
                //                                            substitution_map,
                //                                            free_symbols, 
                //                                            debug);

                if(result.found && result.term_eq)
                    substitution_map.insert({current, result.term_eq});
                else {
                    for(const auto & t : result.terms_for_solving) {
                        if (unsat_count >= 30 && sat_count >= 100) { //FIXME: magic number
                            break;
                        }
                        solver->push();
                        auto eq = solver->make_term(Equal, t, cnode);
                        solver->assert_formula(solver->make_term(Not, eq));
                       
                        std::ostringstream file_name;
                        
                        if (dump_enable) {
                            auto timestamp = std::chrono::high_resolution_clock::now();
                            auto timestamp_ns = std::chrono::duration_cast<std::chrono::nanoseconds>(timestamp.time_since_epoch()).count();
                            fs::path directory = fs::current_path() / "generate";
                            if (!fs::exists(directory)) fs::create_directory(directory);
                            file_name << directory.string() << "/" << timestamp_ns << "_" << file_counter++ << ".smt2";
                            std::ofstream smt2_file(file_name.str());
                            if (smt2_file.is_open()) {
                                solver->dump_smt2(file_name.str());
                                smt2_file.close();
                            }
                        }
                        
                        auto start_time = std::chrono::high_resolution_clock::now();
                        solver->push();
                        solver->set_opt("time-limit", std::to_string(1));
                        auto solver_result = solver->check_sat(); //FIXME time consuming
                        solver->pop();
                        auto end_time = std::chrono::high_resolution_clock::now();
                        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time);
                        auto elapsed = duration.count();
                        count++;

                        if (elapsed >= timeout_ms) {
                            std::cout << "t"; std::cout.flush();
                            total_sat_time += duration;
                            solver->pop();
                            continue;
                        }

                        if (solver_result.is_unsat()) {
                            total_unsat_time += duration;
                            // std::cout << t->to_string() << std::endl;
                            // std::cout << cnode->to_string() << std::endl;
                            // std::cout << "=======================" << std::endl;
                        } else {
                            total_sat_time += duration;
                        }

                        if (solver_result.is_unsat()) {
                            unsat_count++;
                            term_eq = t;
                            if (dump_enable) {
                                std::ofstream smt2_file(file_name.str(), std::ios::app);
                                if (smt2_file.is_open()) {
                                    smt2_file << "UNSAT" << std::endl;
                                    smt2_file.close();
                                }
                            }
                            solver->pop();
                            break;
                        } else {
                            //update_progress(RESULT_SAT);
                            sat_count++;
                            if (dump_enable) {
                                std::ofstream smt2_file(file_name.str(), std::ios::app);
                                if (smt2_file.is_open()) {
                                    smt2_file << "SAT" << std::endl;
                                    smt2_file.close();
                                }
                            }
                            //simualtion counter example
                            fill_simulation_data_for_all_nodes(node_data_map, solver, num_iterations, substitution_map, all_luts);

                        }
                        solver->pop();
                    }
                }

                if (term_eq && term_eq != nullptr) {
                    substitution_map.insert({current, term_eq});
                } else {
                    if (!has_simulation_data(cnode, node_data_map)) {
                        node_data_map[cnode] = std::move(sim_data);
                    }
                    substitution_map.insert({current, cnode});
                    hash_term_map[current_hash].push_back(cnode);
                }
                //update_progress(MAP_UPDATE);
                processed_nodes++;
            } // end if it has children
            node_stack.pop();            
        } // end of if visited
    } // end of traversal
    
    // End of processing - Print summary statistics
    std::cout << std::endl;
    print_hash(hash_term_map);
}