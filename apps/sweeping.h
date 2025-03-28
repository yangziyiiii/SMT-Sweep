#include "assert.h"
#include "config/testpath.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "frontend/btor2_encoder.h"
#include "smt-switch/bitwuzla_factory.h"
#include "smt-switch/identity_walker.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/substitution_walker.h"
#include "smt-switch/utils.h"

#include <iomanip>
#include <chrono>
#include <gmp.h>
#include <gmpxx.h>
#include <iostream>
#include <algorithm>
#include <random>
#include "smt-switch/utils.h"
#include <atomic>
#include <getopt.h>

#include "simulation.h"


#include <filesystem>
#include <fstream>
#include <sstream>
namespace fs = std::filesystem;
static int file_counter = 0;
using namespace smt;
using namespace std;
using namespace wasim;


struct Config {
    std::string btor2_file;
    int simulation_iterations = 0;
    int solver_timeout_ms = 3600000;
    int property_check_timeout_ms = 3600000;
    bool dump_smt = false;
    bool debug = false;
    int bound = 0;
    std::string dump_input_file;
    std::string load_input_file;
};

void print_usage(const char* prog_name) {
    std::cerr << "Usage: " << prog_name << " <BTOR2_FILE_PATH> <SIMULATION_ITERATIONS> [--bound] [--solver_timeout] [--prop_timeout] [--dump_smt] [--debug] [--dump_input] [--load_input]" << std::endl;
    std::cerr << "  --file, -f            : Path to the BTOR2 file (required)" << std::endl;
    std::cerr << "  --iteration, -i       : Number of simulation iterations (required)" << std::endl;
    std::cerr << "  --solver_timeout, -s  : Solver timeout in milliseconds (default: 500000ms)" << std::endl;
    std::cerr << "  --prop_timeout, -p    : Property check timeout in milliseconds (default: 100000ms)" << std::endl;
    std::cerr << "  --bound, -b           : Bound for BMC (default: 0)" << std::endl;
    std::cerr << "  --dump_input, -d      : Dump input simulation data to the file path" << std::endl;
    std::cerr << "  --load_input, -l      : Load input simulation data from the file path" << std::endl;
    std::cerr << "  --dump_smt            : Enable/disable SMT dump (default: disable)" << std::endl;
    std::cerr << "  --debug               : Enable/disable debug information (default: disable)" << std::endl;
    std::cerr << "  --help, -h            : Show this help message" << std::endl;
}

bool parse_arguments(int argc, char* argv[], Config& config) {
    const struct option long_opts[] = {
        {"file", required_argument, nullptr, 'f'},
        {"iteration", required_argument, nullptr, 'i'},
        {"solver_timeout", required_argument, nullptr, 's'},
        {"prop_timeout", required_argument, nullptr, 'p'},
        {"bound", required_argument, nullptr, 'b'},
        {"dump_input", required_argument, nullptr, 'd'},
        {"load_input", required_argument, nullptr, 'l'},
        {"dump_smt", no_argument, nullptr, 1},
        {"debug", no_argument, nullptr, 2},
        {"help", no_argument, nullptr, 'h'},
        {nullptr, 0, nullptr, 0}
    };

    int opt;
    int long_index = 0;
    while ((opt = getopt_long(argc, argv, "f:i:s:p:b:d:l:h", long_opts, &long_index)) != -1) {
        switch (opt) {
            case 'f':
                config.btor2_file = optarg;
                break;
            case 'i':
                config.simulation_iterations = std::atoi(optarg);
                break;
            case 's':
                config.solver_timeout_ms = std::atoi(optarg);
                break;
            case 'p':
                config.property_check_timeout_ms = std::atoi(optarg);
                break;
            case 'b':
                config.bound = std::atoi(optarg);
                break;
            case 'd':
                config.dump_input_file = optarg;
                break;
            case 'l':
                config.load_input_file = optarg;
                break;
            case 1:
                config.dump_smt = true;
                break;
            case 2:
                config.debug = true;
                break;
            case 'h':
                print_usage(argv[0]);
                exit(EXIT_SUCCESS);
            default:
                print_usage(argv[0]);
                return false;
        }
    }

    // Validate required arguments
    if (config.btor2_file.empty() || config.simulation_iterations <= 0) {
        std::cerr << "[ERROR] Missing required arguments: --file and --iteration are mandatory.\n";
        print_usage(argv[0]);
        return false;
    }

    return true;
}



template <typename T, typename... Rest>
inline void hashCombine(std::size_t & seed, T const & v, Rest &&... rest)
{
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
  (int[]){ 0, (hashCombine(seed, std::forward<Rest>(rest)), 0)... };
}


std::chrono::time_point<std::chrono::high_resolution_clock> last_time_point;
void print_time() {
    auto now = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(now - last_time_point).count();
    last_time_point = now;  // Update last time point
    std::cout << "[" << elapsed_time / 1000.0 << " s]  ";
}


class NodeData {
private:
    Term term;
    size_t bit_width;
    std::vector<BtorBitVector> simulation_data; //TODO: memory usage
public:
    NodeData() : term(nullptr), bit_width(0) {} 

    NodeData(const Term & t) : term(t), bit_width(0) {}

    NodeData(const Term & t, const size_t & bw) : term(t), bit_width(bw) {}

    Term get_term() const { return term; }
    
    size_t get_bit_width() const { return bit_width; }
    
    std::vector<BtorBitVector>& get_simulation_data() {
        return simulation_data;
    }
    const std::vector<BtorBitVector>& get_simulation_data() const {
        return simulation_data;
    }

    size_t hash() const {
        return hash(simulation_data);
    }

    static size_t hash(const std::vector<BtorBitVector>& data) {
        if (data.empty()) {
            return 0;
        }

        size_t hash_val = 0;
        for(const auto & v : data) {
            auto clean_val = std::string(btor_bv_to_char(&v));
            assert(clean_val.substr(0, 2) != "#b");
            hashCombine(hash_val, clean_val);
        }
        return hash_val;
    }
};

void create_lut(Term current, std::unordered_map<std::string, std::string>& lut) {
    while (current->get_op().prim_op == PrimOp::Store) {
        auto children = TermVec(current->begin(), current->end());
        if (children.size() != 3) {
            throw std::runtime_error("Store operation should have exactly 3 children");
        }
        // store：array、index、value
        auto array = children[0];   // original array
        auto index = children[1];   // stored position
        auto value = children[2];   // sotred value

        // std::cout<< "stored position:" <<std::endl;
        // std::cout<< "stored position" << index->to_string().c_str() << std::endl;
        // std::cout<< "stored value" << value->to_string().c_str() << std::endl;
        
        lut[index->to_string().substr(2)] = value->to_string().substr(2);

        current = children[0]; // next iteration
    }
}


void btor_bv_operation_1child(const smt::Op& op, 
                              const BtorBitVector& btor_child_1, 
                              NodeData &nd) {    
    if(op.prim_op == PrimOp::Not) {
        auto current_val = btor_bv_not(&btor_child_1);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNot) {
        auto current_val = btor_bv_not(&btor_child_1);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Extract) {
        auto high = op.idx0;
        auto low = op.idx1;
        assert(high >= low);
        // cout << "btor_child_1: " << btor_child_1.bits << ", width: " << btor_child_1.width << ", length: " << btor_child_1.len << endl;
        // cout << "btor_child_1: " << btor_child_1.val << ", width: " << btor_child_1.width << endl;
        auto current_val = btor_bv_slice(&btor_child_1, high, low);
        assert(current_val->width == high - low + 1);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Zero_Extend) {
        auto current_val = btor_bv_uext(&btor_child_1, op.idx0);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Sign_Extend) {
        auto current_val = btor_bv_sext(&btor_child_1, op.idx0);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNeg) {
        auto current_val = btor_bv_neg(&btor_child_1);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        cout << "Unsupported operation type 1 child: " << op.to_string() << endl;
        throw NotImplementedException("Unsupported operation type 1 child: " + op.to_string());
    }
}

void btor_bv_operation_2children(const smt::Op& op, 
                                 const BtorBitVector& btor_child_1, 
                                 const BtorBitVector& btor_child_2, 
                                 NodeData &nd) {
    if(op.prim_op == PrimOp::BVAdd) {
        auto current_val = btor_bv_add(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    } 
    else if(op.prim_op == PrimOp::BVAnd) {
        auto current_val = btor_bv_and(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::And) {
        auto current_val = btor_bv_and(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Concat) {
        auto current_val = btor_bv_concat(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Equal) {
        auto current_val = btor_bv_eq(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVXor) {
        auto current_val = btor_bv_xor(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Xor) {
        auto current_val = btor_bv_xor(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Or) {
        auto current_val = btor_bv_or(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVOr) {
        auto current_val = btor_bv_or(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVMul) {
        auto current_val = btor_bv_mul(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVComp) {
        auto current_val = btor_bv_compare(&btor_child_1, &btor_child_2);
        auto current_val_bv = btor_bv_int64_to_bv(current_val, 1);
        nd.get_simulation_data().push_back(*current_val_bv);
    }
    else if(op.prim_op == PrimOp::Distinct) {
        auto current_val = btor_bv_ne(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUdiv) {
        auto current_val = btor_bv_udiv(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSub) {
        auto current_val = btor_bv_sub(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUlt) {
        auto current_val = btor_bv_ult(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUle) {
        auto current_val = btor_bv_ulte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUgt) {
        auto current_val = btor_bv_ugt(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUge) {
        auto current_val = btor_bv_ugte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSlt) {
        auto current_val = btor_bv_slt(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSle) {
        auto current_val = btor_bv_slte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSgt) {
        auto current_val = btor_bv_sgt(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSge) {
        auto current_val = btor_bv_sgte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNand) {
        auto current_val = btor_bv_nand(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNor) {
        auto current_val = btor_bv_nor(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVXnor) {
        auto current_val = btor_bv_xnor(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUrem) {
        auto current_val = btor_bv_urem(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSdiv) {
        auto current_val = btor_bv_sdiv(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSrem) {
        auto current_val = btor_bv_srem(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVLshr) {
        auto current_val = btor_bv_srl(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVAshr) {
        auto current_val = btor_bv_sra(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVShl) {
        auto current_val = btor_bv_sll(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Implies) {
        auto current_val = btor_bv_implies(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        cout << "Unsupported operation type 2 children: " << op.to_string() << endl;
        throw NotImplementedException("Unsupported operation type 2 children: " + op.to_string());
    }
}

void btor_bv_operation_3children(const smt::Op& op, 
                                 const BtorBitVector& btor_child_1, 
                                 const BtorBitVector& btor_child_2,
                                 const BtorBitVector& btor_child_3,
                                 NodeData &nd) {
    if(op.prim_op == PrimOp::Ite) {
        auto current_val = btor_bv_ite(&btor_child_1, &btor_child_2, &btor_child_3);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        cout << "Unsupported operation type 3 children: " << op.to_string() << endl;
        throw NotImplementedException("Unsupported operation type 3 children: " + op.to_string());
    }
}


//one child simulation
void process_single_child_simulation(const Term & child,
                                     int & num_iterations,
                                     const smt::Op& op_type,
                                     const std::unordered_map<Term, NodeData> & node_data_map,
                                     NodeData & out,
                                     bool debug = false) {
    assert(child->get_sort()->get_sort_kind() != ARRAY);

    const auto & sim_data = node_data_map.at(child).get_simulation_data();

    if (debug && sim_data.size() != (size_t)num_iterations) {
        std::ostringstream oss;
        oss << "[Simulation Error] sim_data.size() = " << sim_data.size()
            << ", expected num_iterations = " << num_iterations;
        throw std::runtime_error(oss.str());
    }

    for(size_t i = 0; i < (size_t)num_iterations; i++) {
        const auto & bv_child = sim_data[i];
        btor_bv_operation_1child(op_type, bv_child, out);
    }

    assert(out.get_simulation_data().size() == (size_t)num_iterations);
}
//two children simulation
void process_two_children_simulation(const smt::TermVec & children,
                                     int & num_iterations, 
                                     const smt::Op& op_type, 
                                     const std::unordered_map<Term, NodeData>& node_data_map,
                                     const std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                                     NodeData& nd, /* OUTPUT */
                                     bool debug = false
                                     ) { 

     if (op_type.prim_op == PrimOp::Select) {  // Array operation (Select)
        const auto& array_var = children[0];
        const auto& index_term = children[1];

        // std::cout << "Looking for array: " << array->to_string() << std::endl;
        assert(all_luts.find(array_var) != all_luts.end());

        const auto& sim_data_index = node_data_map.at(index_term).get_simulation_data();

        if (debug && sim_data_index.size() != static_cast<size_t>(num_iterations)) {
            std::ostringstream oss;
            oss << "[Simulation Error] sim_data_index.size() = " << sim_data_index.size()
                << ", expected num_iterations = " << num_iterations;
            throw std::runtime_error(oss.str());
        }

        for (size_t i = 0; i < num_iterations; ++i) {
            // Resolve the simulation data for the index child (if substitution happened, we use resolved node)

            auto index_str = std::string(btor_bv_to_char( & (sim_data_index[i])));
            const auto & val_str = all_luts.at(array_var).at(index_str);
            // cout << "index: " << index_str << ", value: " << val_str << endl;
            auto val = btor_bv_char_to_bv(val_str.data());
            nd.get_simulation_data().push_back(*val);
        }

    }else { // for other bit-vector operations
        const auto& child_1 = children[0];
        const auto& child_2 = children[1];

        // If substitution happened, we must get the resolved node and use its simulation data
        const auto& sim_data_1 = node_data_map.at(child_1).get_simulation_data();
        const auto& sim_data_2 = node_data_map.at(child_2).get_simulation_data();
        
        //debug
        if (debug) {
            if (sim_data_1.size() != static_cast<size_t>(num_iterations)) {
                std::ostringstream oss;
                oss << "[Simulation Error] sim_data_1 size mismatch detected!\n"
                    << "  - sim_data_1.size(): " << sim_data_1.size() << "\n"
                    << "  - expected num_iterations: " << num_iterations;
                throw std::runtime_error(oss.str());
            }
            if (sim_data_2.size() != static_cast<size_t>(num_iterations)) {
                std::ostringstream oss;
                oss << "[Simulation Error] sim_data_2 size mismatch detected!\n"
                    << "  - sim_data_2.size(): " << sim_data_2.size() << "\n"
                    << "  - expected num_iterations: " << num_iterations;
                throw std::runtime_error(oss.str());
            }
        }

        // Perform the operation on the simulation data
        for (size_t i = 0; i < num_iterations; ++i) {
            const auto& btor_child_1 = sim_data_1[i];
            const auto& btor_child_2 = sim_data_2[i];
            btor_bv_operation_2children(op_type, btor_child_1, btor_child_2, nd);
        }
    }

    assert(nd.get_simulation_data().size() == num_iterations);
}

// three children simulation
void process_three_children_simulation(const smt::TermVec& children, 
                                       int & num_iterations, 
                                       const smt::Op& op_type, 
                                       const std::unordered_map<Term, NodeData>& node_data_map,
                                       const std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                                       NodeData& nd,
                                       bool debug = false) {

    // Now, handle the simulation data and apply the operator
    // Resolve the simulation data for each child (if substitution happened, we use resolved node)
    const auto& sim_data_1 = node_data_map.at(children[0]).get_simulation_data();
    const auto& sim_data_2 = node_data_map.at(children[1]).get_simulation_data();
    const auto& sim_data_3 = node_data_map.at(children[2]).get_simulation_data();

    //debug
    if (debug) {
        if (sim_data_1.size() != static_cast<size_t>(num_iterations)) {
            std::ostringstream oss;
            oss << "[Simulation Error] sim_data_1 size mismatch detected!\n"
                << "  - sim_data_1.size(): " << sim_data_1.size() << "\n"
                << "  - expected num_iterations: " << num_iterations;
            throw std::runtime_error(oss.str());
        }
        if (sim_data_2.size() != static_cast<size_t>(num_iterations)) {
            std::ostringstream oss;
            oss << "[Simulation Error] sim_data_2 size mismatch detected!\n"
                << "  - sim_data_2.size(): " << sim_data_2.size() << "\n"
                << "  - expected num_iterations: " << num_iterations;
            throw std::runtime_error(oss.str());
        }
        if (sim_data_3.size() != static_cast<size_t>(num_iterations)) {
            std::ostringstream oss;
            oss << "[Simulation Error] sim_data_3 size mismatch detected!\n"
                << "  - sim_data_3.size(): " << sim_data_3.size() << "\n"
                << "  - expected num_iterations: " << num_iterations;
            throw std::runtime_error(oss.str());
        }
    }

    for (size_t i = 0; i < num_iterations; i++) {
        // Retrieve the bit-vector data for each child at the current iteration
        auto btor_child_1 = sim_data_1[i];
        auto btor_child_2 = sim_data_2[i];
        auto btor_child_3 = sim_data_3[i];
        // Apply the operator
        btor_bv_operation_3children(op_type, btor_child_1, btor_child_2, btor_child_3, nd);
    }

    assert(nd.get_simulation_data().size() == num_iterations);
}


// main simulation function
void compute_simulation(
                      const smt::TermVec & children, 
                      int& num_iterations, 
                      const smt::Op& op_type, 
                      const std::unordered_map<Term, NodeData>& node_data_map,
                      const std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts, 
                      NodeData& nd // output
                      ) {
    if (children.size() == 1) {
        process_single_child_simulation(children[0], num_iterations, op_type, node_data_map, nd);
    } else if (children.size() == 2) {
        process_two_children_simulation(children, num_iterations, op_type, node_data_map, all_luts, nd);
    } else if(children.size() == 3) {
        process_three_children_simulation(children, num_iterations, op_type, node_data_map, all_luts, nd);
    } else {
        throw std::runtime_error("[Simulation Error] Unsupported number of children: " + std::to_string(children.size()));
    }
}

void children_substitution(const smt::TermVec& children, smt::TermVec& out, const std::unordered_map<Term, Term>& substitution_map) {
	for (const auto & c : children) {
        auto pos = substitution_map.find(c);
        assert(pos != substitution_map.end());
        out.push_back(pos->second);
	}
} // end of children_substitution



// RAII wrapper for GMP random state
class GmpRandStateGuard
{
    gmp_randstate_t state;

    public:
    GmpRandStateGuard()
    {
        gmp_randinit_default(state);
        gmp_randseed_ui(state, time(NULL));
    }

    ~GmpRandStateGuard() { gmp_randclear(state); }

    void random_input(mpz_t & rand_num, int num)
    {
        mpz_init2(rand_num, num);
        mpz_urandomb(rand_num, state, num);
    }

    // operator gmp_randstate_t &() { return state; }
};

void initialize_arrays(const std::vector<TransitionSystem*>& systems,
                       std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                       std::unordered_map<Term, Term>& substitution_map,
                       bool & debug
) {
    for (auto* sts : systems) {
        for (const auto& var_val_pair : sts->init_constants()) {
            if (var_val_pair.first->get_sort()->get_sort_kind() != ARRAY) continue;
            Term var = var_val_pair.first;
            Term val = var_val_pair.second;
            if (all_luts.find(var) == all_luts.end()) {
                create_lut(val, all_luts[var]);
                if(debug) {
                    std::cout << "[array create] " << var->to_string() << " of size " << all_luts[var].size() << std::endl;
                }
            }
        }
    }

    // Array comparison
    for (auto pos = all_luts.begin(); pos != all_luts.end(); ++ pos) {
        const auto & array_var_i = pos->first;
        auto array_size_i = pos->second.size();
        const auto & idx_val_i = pos->second;
        bool another_array_found = false;
        for (auto pos_j = all_luts.begin(); pos_j != pos; ++pos_j ) {
            auto array_size_j = pos_j->second.size();
            if (array_size_j != array_size_i)
                continue;
            const auto & idx_val_j = pos_j->second;
            bool all_equal = true;
            for (const auto & idx_val_pair : idx_val_i) {
                auto elem_pos = idx_val_j.find(idx_val_pair.first);
                if (elem_pos == idx_val_j.end()) {
                    // no such index
                    all_equal = false;
                    break;
                }
                if (elem_pos->second != idx_val_pair.second) {
                    all_equal = false;
                    break;
                }
            }
            if (!all_equal)
                continue;
            // if equal
            const auto & array_var_j = pos_j->first;
            // std::cout << "[sub array] " << array_var_i ->to_string() << " --> " << array_var_j->to_string() << std::endl;
            substitution_map.insert({array_var_i, array_var_j});
            another_array_found = true;
            // if you find one then it is okay, no need to find the rest
            break;
            // in case multiple pairs exists
            // 0 , 1, 2   . then 2-->0  1-->0
        }
        if (!another_array_found) {
            // std::cout << "[array not sub] " << array_var_i ->to_string() << std::endl;
            substitution_map.insert({array_var_i, array_var_i});
        }
    }
}

void match_term_constraint_pattern(const smt::TermVec & constraints,
                                     std::unordered_map<Term, std::string> & constraint_input_map)
{
    // std::cout << "[Constraint Matching] Raw constraints:\n";
    // for (const auto & c : constraints) {
    //     std::cout << c->to_string() << std::endl;
    // }

    auto extract_val = [](const Term & term) -> std::string {
        return term->to_string().substr(2);
    };

    auto try_add_entry = [&](const Term & sym_term, const Term & const_term) {
        if (!sym_term || !const_term || !sym_term->is_symbolic_const() || !const_term->is_value()) return;
        constraint_input_map[sym_term] = extract_val(const_term);
        // std::cout << "[Constraint Mapping] " << sym_term->to_string() << " == " << extract_val(const_term) << std::endl;
    };

    std::function<void(const Term&)> recursive_match;
    recursive_match = [&](const Term & t) {
        if (t->get_op().prim_op == smt::Equal) {
            smt::TermVec children(t->begin(), t->end());
            if (children.size() != 2) return;
            Term lhs = children[0];
            Term rhs = children[1];

            try_add_entry(lhs, rhs);
            try_add_entry(rhs, lhs);

            if (lhs->get_op().prim_op == smt::BVComp && rhs->is_value() && extract_val(rhs) == "1") {
                smt::TermVec bvcomp_children(lhs->begin(), lhs->end());
                if (bvcomp_children.size() != 2) return;
                Term comp_lhs = bvcomp_children[0];
                Term comp_rhs = bvcomp_children[1];
                try_add_entry(comp_lhs, comp_rhs);
                try_add_entry(comp_rhs, comp_lhs);
            }

            if (lhs->get_op().prim_op == smt::Extract && rhs->is_value()) {
                smt::TermVec extract_children(lhs->begin(), lhs->end());
                if (extract_children.size() != 1) return;
                Term extract_term = extract_children[0];
                if (!extract_term->is_symbolic_const()) return;
                uint64_t high = lhs->get_op().idx0;
                uint64_t low  = lhs->get_op().idx1;
                std::string rhs_val = extract_val(rhs);
                constraint_input_map[extract_term] = "EXTRACT_" + std::to_string(high) + "_" + std::to_string(low) + "=" + rhs_val;
                std::cout << "[Constraint Mapping] EXTRACT -> " << extract_term->to_string()
                          << ", bits " << high << ":" << low << " = " << rhs_val << std::endl;
            }

            if (lhs->get_op().prim_op == smt::Ite) recursive_match(lhs);
            if (rhs->get_op().prim_op == smt::Ite) recursive_match(rhs);
        }
        else if (t->get_op().prim_op == smt::Ite) {
            for (auto it = t->begin(); it != t->end(); ++it) {
                recursive_match(*it);
            }
        }
    };

    for (const auto & constraint : constraints)
        recursive_match(constraint);
}


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
                node_data_map[term].get_simulation_data().push_back(*bv_input);
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
                node_data_map[it->second].get_simulation_data().push_back(*bv_input);
            }
        }
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
            node_data_map[term].get_simulation_data().push_back(*bv_input);
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



void count_total_nodes(const smt::Term& root, int& total_nodes) {
    std::stack<Term> count_stack;
    std::unordered_set<Term> visited;
    count_stack.push(root);
    while (!count_stack.empty()) {
        Term current = count_stack.top();
        count_stack.pop();
        if (visited.count(current)) continue;
        visited.insert(current);
        total_nodes++;
        for (auto child : current) {
            if (child->get_sort()->get_sort_kind() == BV || child->get_sort()->get_sort_kind() == BOOL) {
                count_stack.push(child);
            }
        }
    }
}


void simulate_constant_node(const smt::Term& current, 
                            int & num_iterations, 
                            std::unordered_map<Term, NodeData>& node_data_map) {
    if (current->get_sort()->get_sort_kind() == BOOL) {
        std::string val_str = current->to_string(); // "true" / "false"
        std::string bitval = (val_str == "true") ? "1" : "0";
        auto current_bv = btor_bv_char_to_bv(bitval.c_str());
        for (int i = 0; i < num_iterations; ++i)
            node_data_map[current].get_simulation_data().push_back(*current_bv);
    } else {
        std::string current_str = current->to_string().substr(2);
        auto current_bv = btor_bv_char_to_bv(current_str.data());
        assert(current_bv->width == current->get_sort()->get_width());
        for (int i = 0; i < num_iterations; ++i)
            node_data_map[current].get_simulation_data().push_back(*current_bv);
    }
    assert(node_data_map[current].get_simulation_data().size() == num_iterations);
}


void simulate_leaf_node(const smt::Term& current, 
                        int & num_iterations, 
                        std::unordered_map<Term, NodeData>& node_data_map,
                        std::string & dump_file_path,
                        std::string & load_file_path) {
    if (node_data_map.find(current) == node_data_map.end()) {
        simulation(TermVec{current}, num_iterations, node_data_map, dump_file_path, load_file_path);
    }
    assert(node_data_map[current].get_simulation_data().size() == num_iterations);
}



struct TryFindResult {
    bool found;
    Term term_eq;
    TermVec terms_for_solving;
};

TryFindResult try_find_equiv_term(const Term & cnode,
                                  const uint32_t & current_hash,
                                  const NodeData & sim_data,
                                  int & num_iterations,
                                  const std::unordered_map<uint32_t, TermVec> & hash_term_map,
                                  const std::unordered_map<Term, NodeData> & node_data_map,
                                  const std::unordered_map<Term, Term> & substitution_map,
                                  bool & debug) {
    TryFindResult result {false, nullptr, {}};

    if (hash_term_map.find(current_hash) == hash_term_map.end()) return result;
    const auto & terms_to_check = hash_term_map.at(current_hash);
    const auto & sim_data_vec = sim_data.get_simulation_data();
    size_t size = terms_to_check.size();
    

    //partial vector to minimize the number of terms to check
    smt::TermVec filtered_terms;
    std::mt19937 rng(std::random_device{}());

    if (size <= 4) {
        filtered_terms = terms_to_check;
    }
    else if (size <= 10) {
        if (size >= 6) {
            filtered_terms.insert(filtered_terms.end(), terms_to_check.begin(), terms_to_check.begin() + 3);
            filtered_terms.insert(filtered_terms.end(), terms_to_check.end() - 3, terms_to_check.end());
        } else {
            size_t first = std::min(size_t(2), size);
            size_t last = std::min(size_t(2), size - first);
            filtered_terms.insert(filtered_terms.end(), terms_to_check.begin(), terms_to_check.begin() + first);
            filtered_terms.insert(filtered_terms.end(), terms_to_check.end() - last, terms_to_check.end());
        }
    }
    else {
        size_t prefix_count = 0, suffix_count = 0, max_middle_sample = 0, cap = 20;

        if (size <= 30) {
            prefix_count = std::min(size_t(4), size);
            suffix_count = std::min(size_t(4), size - prefix_count);
            max_middle_sample = std::min(size - prefix_count - suffix_count, size_t(4));
            cap = 12;
        } else if (size <= 50) {
            prefix_count = std::min(size_t(5), size);
            suffix_count = std::min(size_t(5), size - prefix_count);
            max_middle_sample = std::min(size - prefix_count - suffix_count, size_t(5));
            cap = 15;
        } else if (size <= 100) {
            prefix_count = std::min(size_t(5), size);
            suffix_count = std::min(size_t(5), size - prefix_count);
            max_middle_sample = std::min(size_t(8), size - prefix_count - suffix_count);
            cap = 18;
        } else {
            prefix_count = std::min(size_t(5), size);
            suffix_count = std::min(size_t(5), size - prefix_count);
            max_middle_sample = std::min(size_t(10), size - prefix_count - suffix_count);
            cap = 20;
        }

        smt::TermVec prefix, suffix, middle_sample;

        prefix.insert(prefix.end(), terms_to_check.begin(), terms_to_check.begin() + prefix_count);
        suffix.insert(suffix.end(), terms_to_check.end() - suffix_count, terms_to_check.end());

        auto middle_start = terms_to_check.begin() + prefix_count;
        auto middle_end   = terms_to_check.end() - suffix_count;
        smt::TermVec middle(middle_start, middle_end);

        std::sample(middle.begin(), middle.end(),
                    std::back_inserter(middle_sample),
                    max_middle_sample, rng);

        filtered_terms.reserve(prefix.size() + middle_sample.size() + suffix.size());
        filtered_terms.insert(filtered_terms.end(), prefix.begin(), prefix.end());
        filtered_terms.insert(filtered_terms.end(), middle_sample.begin(), middle_sample.end());
        filtered_terms.insert(filtered_terms.end(), suffix.begin(), suffix.end());

        if (filtered_terms.size() > cap) {
            filtered_terms.resize(cap);
        }
    }

    for (const auto & t : filtered_terms) {
        if (t == cnode) {
            result.found = true;
            result.term_eq = t;
            return result;
        }
        
        if (t->get_sort() != cnode->get_sort()) {
            continue;
        }

        if (node_data_map.find(t) == node_data_map.end()) {
            std::ostringstream oss;
            oss << "[Missing Data] Simulation data not found in node_data_map for term:\n"
                << "  - Term: " << t;
            std::cerr << oss.str() << std::endl;
            continue;
        }
        
        const auto & existing_sim_data = node_data_map.at(t).get_simulation_data();
        bool match = true;
        for (int i = 0; i < num_iterations; ++i) {
            if (btor_bv_compare(&existing_sim_data[i], &sim_data_vec[i]) != 0) {
                match = false;
                break;
            }
        }
        if (match) {
            result.terms_for_solving.push_back(t);
        }
    }

    return result;
}

void print_hash(const std::unordered_map<uint32_t, smt::TermVec>& hash_term_map) {
    std::cout << "Sweeping Summary Statistics:" << std::endl;
    std::cout << "============================" << std::endl;

    int total_terms = 0;
    std::vector<std::pair<uint32_t, size_t>> hash_frequencies;

    for (const auto& [hash_value, terms] : hash_term_map) {
        hash_frequencies.emplace_back(hash_value, terms.size());
        total_terms += terms.size();
    }

    std::sort(hash_frequencies.begin(), hash_frequencies.end(),
              [](const auto& a, const auto& b) { return a.second > b.second; });

    std::cout << "Total unique hash values: " << hash_term_map.size() << std::endl;
    std::cout << "Total terms processed: " << total_terms << std::endl;
    std::cout << "Shared hash value ratio: "
              << std::fixed << std::setprecision(2)
              << ((float)(total_terms - hash_term_map.size()) / total_terms * 100.0) << "%" << std::endl;

    std::cout << std::endl;
    std::cout << "Top 5 Hash Values by Term Frequency:" << std::endl;
    std::cout << "-----------------------------------" << std::endl;
    std::cout << std::setw(12) << "Hash Value" << " | "
              << std::setw(10) << "Term Count" << " | "
              << std::setw(10) << "% of Total" << std::endl;
    std::cout << "-----------------------------------" << std::endl;

    int to_display = std::min(5, static_cast<int>(hash_frequencies.size()));
    for (int i = 0; i < to_display; ++i) {
        const auto& [hash_value, count] = hash_frequencies[i];
        float percentage = (float)count / total_terms * 100.0;
        std::cout << std::setw(12) << hash_value << " | "
                  << std::setw(10) << count << " | "
                  << std::setw(9) << std::fixed << std::setprecision(2) << percentage << "%" << std::endl;
    }

    std::cout << "============================" << std::endl;
    std::cout << "Sweeping done, begin the last solving using bitwuzla for this property" << std::endl;
}


void pre_collect_constants(const std::vector<Term>& traversal_roots,
                            std::unordered_map<Term, NodeData>& node_data_map,
                            std::unordered_map<uint32_t, TermVec>& hash_term_map,
                            std::unordered_map<Term, Term>& substitution_map,
                            const int & num_iterations)
{
    std::stack<Term> stack;
    std::unordered_set<Term> visited;
    for (const auto &root : traversal_roots) {
        stack.push(root);
    }
    while (!stack.empty()) {
        Term current = stack.top();
        stack.pop();
        if (visited.find(current) != visited.end())
            continue;
        visited.insert(current);

        if (substitution_map.find(current) != substitution_map.end())
            continue;

        if (current->is_value()) {
            if(current->get_sort()->get_sort_kind() == BOOL){
                std::string val_str = current->to_string(); // "true" / "false"
                std::string bitval = (val_str == "true") ? "1" : "0";
                auto current_bv = btor_bv_char_to_bv(bitval.c_str());
                for (int i = 0; i < num_iterations; ++i)
                    node_data_map[current].get_simulation_data().push_back(*current_bv);
            } else {
                std::string current_str = current->to_string().substr(2);
                auto current_bv = btor_bv_char_to_bv(current_str.data());
                if(node_data_map[current].get_simulation_data().empty()){
                    for (int i = 0; i < num_iterations; ++i) {
                        node_data_map[current].get_simulation_data().push_back(*current_bv);
                    }
                }
            }
            substitution_map.insert({current, current});
            hash_term_map[node_data_map[current].hash()].push_back(current);
        }

        for (auto child : current) {
            stack.push(child);
        }
    }
}

bool check_prop(const Term & p, const TermVec & asmpt, SmtSolver & solver)
{
    solver->push();
    for (const auto & a : asmpt) {
        solver->assert_formula(a);
    }
    solver->assert_formula(solver->make_term(Not, p));
    // solver->dump_smt2("spi_1_10.smt2"); //FIXME

    auto res = solver->check_sat();
    solver->pop();
    return res.is_unsat();
}


static Term and_vec(const TermVec & v, SmtSolver & solver)
{
    if (v.empty()) return solver->make_term(true);
    if (v.size() == 1) return v.at(0);

    auto ret = v.at(0);
    for (size_t idx = 1; idx < v.size(); ++idx)
        ret = solver->make_term(smt::And, ret, v.at(idx));
    return ret;
}


bool all_substituted(const TermVec& children, 
                    const std::unordered_map<Term, Term>& subst_map) {
    for (const auto & c : children) {
        if (subst_map.find(c) == subst_map.end())
            return false;
    }
    return true;
}


void fill_simulation_data_for_all_nodes(std::unordered_map<Term, NodeData>& node_data_map,
                                        SmtSolver& solver,
                                        int num_iterations,
                                        std::unordered_map<Term, Term>& substitution_map,
                                        const std::unordered_map<Term, std::unordered_map<std::string, std::string>> & all_luts)
{
    for (auto& [term, nd] : node_data_map) {
        auto& sim_vec = nd.get_simulation_data();
        int current_size = sim_vec.size();
        if (current_size >= num_iterations) continue;

        int width = term->get_sort()->get_width();

        if (term->is_value()) {
            std::string val_str = (term->get_sort()->get_sort_kind() == BOOL)
                ? ((term->to_string() == "true") ? "1" : "0")
                : term->to_string().substr(2);
            auto bv = btor_bv_char_to_bv(val_str.c_str());
            for (int i = current_size; i < num_iterations; ++i)
                sim_vec.push_back(*bv);
        } else if (term->is_symbolic_const() && term->get_op().is_null()) {
            Term val = solver->get_value(term);
            std::string val_str = (term->get_sort()->get_sort_kind() == BOOL)
                ? ((val->to_string() == "true") ? "1" : "0")
                : val->to_string().substr(2);
            BtorBitVector bv_val = *btor_bv_char_to_bv(val_str.c_str());
            sim_vec.push_back(bv_val);
        } else {
            TermVec children(term->begin(), term->end());
            TermVec substituted;
            children_substitution(children, substituted, substitution_map);
            NodeData temp_sim;
            int one_iter = 1;
            compute_simulation(substituted, one_iter, term->get_op(), node_data_map, all_luts, temp_sim);
            sim_vec.push_back(temp_sim.get_simulation_data().front());
        }

        if (sim_vec.size() != (size_t)num_iterations) {
            std::cerr << "[FATAL] Post-fill simulation_data size mismatch for term: "
                      << term->to_string() << " size: " << sim_vec.size() << " vs expected: " << num_iterations << std::endl;
            exit(EXIT_FAILURE);
        }
    }
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
                std::chrono::milliseconds& total_unsat_time)
{
    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});
    std::unordered_map<Term, BtorBitVector> sat_data_buffer;

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
    count_total_nodes(root, total_nodes); //FIXME this may causes more time
    std::cout << "Begin sweeping with " << total_nodes << " nodes..." << std::endl;

    // Function to update and display progress
    auto update_progress = [&](SweepingStep step) {
        current_step = step;
        const int bar_width = 50;
        float progress = (float)processed_nodes / total_nodes;
        
        std::cout << "\r[";
        int pos = bar_width * progress;
        for (int i = 0; i < bar_width; ++i) {
            if (i < pos) std::cout << "=";
            else if (i == pos) std::cout << ">";
            else std::cout << " ";
        }
        std::cout << "] " << int(progress * 100.0) << "% | "
                  << "Step: " << step_names[step] << " | "
                  << processed_nodes << "/" << total_nodes << " nodes"
                  << std::flush;
    };

    while(!node_stack.empty()) {
        auto & [current,visited] = node_stack.top();
        // cout << "current: " << current ->to_string() << endl;
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
                update_progress(CONST_NODE);
                simulate_constant_node(current, num_iterations, node_data_map);
                substitution_map.insert({current, current});
                hash_term_map[node_data_map[current].hash()].push_back(current);
                processed_nodes++;
            } 

            else if(current->is_symbolic_const() && current->get_op().is_null()) { // leaf nodes
                update_progress(LEAF_NODE);
                assert(TermVec(current->begin(), current->end()).empty());// no children
                assert(current->get_sort()->get_sort_kind() != ARRAY); // no array
                simulate_leaf_node(current, num_iterations, node_data_map, dump_file_path, load_file_path);
                substitution_map.insert({current, current}); 
                processed_nodes++;
            }
            
            else { // compute simulation data for current node
                TermVec children(current->begin(), current->end()); // find children
                auto child_size = children.size();

                update_progress(FIND_CHILD);
                bool substitution_happened = false;
                TermVec children_substituted;
                children_substitution(children, children_substituted, substitution_map);
                assert(children_substituted.size() == child_size);
                for (size_t i = 0; i < child_size; ++ i)
                    if (children_substituted.at(i) != children.at(i)) {
                        substitution_happened = true;
                        break;
                    }
                
                auto op_type = current->get_op();
                Term cnode = substitution_happened ? solver->make_term(op_type, children_substituted) : current;

                NodeData sim_data;
                Term term_eq = nullptr; 
                compute_simulation(children_substituted, num_iterations, op_type, node_data_map, all_luts, sim_data);
                auto current_hash = sim_data.hash();

                update_progress(EQUIV_CHECK);
                TryFindResult result = try_find_equiv_term(cnode, 
                                                                 current_hash, 
                                                                 sim_data, 
                                                                 num_iterations, 
                                                                 hash_term_map, 
                                                                 node_data_map, 
                                                                 substitution_map, 
                                                                 debug);

                if(result.found && result.term_eq)
                    substitution_map.insert({current, result.term_eq});
                else {
                    for(const auto & t : result.terms_for_solving) {
                        if (unsat_count >= 100 && sat_count >= 100) break; //FIXME magic
                        solver->push();
                        try {
                            auto eq = solver->make_term(Equal, t, cnode);
                            solver->assert_formula(solver->make_term(Not, eq));
                        } catch (const std::exception& e) {
                            std::cerr << "[Equal-Term-Error] " << e.what() << "\n";
                            solver->pop();
                            continue;
                        }
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
                        auto solver_result = solver->check_sat(); //FIXME time consuming
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
                            update_progress(RESULT_SAT);
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
                    substitution_map.insert({current, cnode});
                    hash_term_map[current_hash].push_back(cnode);
                    node_data_map[cnode] = sim_data;
                }
                update_progress(MAP_UPDATE);
                processed_nodes++;
            } // end if it has children
            node_stack.pop();            
        } // end of if visited
    } // end of traversal
    
    // End of processing - Print summary statistics
    std::cout << std::endl;
    print_hash(hash_term_map);
}