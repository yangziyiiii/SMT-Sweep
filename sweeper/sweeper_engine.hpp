#pragma once
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <stack>
#include <string>
#include <chrono>
#include "sweeper/config.hpp"
#include "sweeper/node_data.hpp"
#include "sweeper/simulation_engine.hpp"

namespace sweeper {

// pre-collect constants
void pre_collect_constants(const std::vector<smt::Term>& traversal_roots,
                           std::unordered_map<smt::Term, NodeData>& node_data_map,
                           std::unordered_map<uint32_t, smt::TermVec>& hash_term_map,
                           std::unordered_map<smt::Term, smt::Term>& substitution_map,
                           const int & num_iterations);

// post-order sweeping 主过程
void post_order(const smt::Term & root,
                std::unordered_map<smt::Term, NodeData> & node_data_map,
                std::unordered_map<uint32_t, smt::TermVec> & hash_term_map,
                std::unordered_map<smt::Term, smt::Term> & substitution_map,
                const std::unordered_map<smt::Term, std::unordered_map<std::string, std::string>> & all_luts,
                int & count, int & unsat_count, int & sat_count,
                smt::SmtSolver & solver, int & num_iterations, bool dump_enable,
                int timeout_ms, bool debug,
                std::string & dump_file_path, std::string & load_file_path,
                std::chrono::milliseconds & total_sat_time,
                std::chrono::milliseconds & total_unsat_time,
                std::chrono::milliseconds & ordering_time);

} // namespace sweeper
