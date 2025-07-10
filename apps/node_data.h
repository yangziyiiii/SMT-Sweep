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

#include "config.h"
#include "simulation.h"

#include <filesystem>
#include <fstream>
#include <sstream>
namespace fs = std::filesystem;
static int file_counter = 0;
using namespace smt;
using namespace std;
using namespace wasim;


class NodeData {
private:
    Term term;
    size_t bit_width;
    std::vector<BtorBitVectorPtr> simulation_data;
public:
    NodeData() : term(nullptr), bit_width(0) {} 

    NodeData(const Term & t) : term(t), bit_width(0) {}

    NodeData(const Term & t, const size_t & bw) : term(t), bit_width(bw) {}

    NodeData(const NodeData&) = delete;
    NodeData& operator=(const NodeData&) = delete;

    NodeData(NodeData&&) noexcept = default;
    NodeData& operator=(NodeData&&) noexcept = default;

    Term get_term() const noexcept { return term; }
    size_t get_bit_width() const noexcept { return bit_width; }
    
    std::vector<BtorBitVectorPtr>& get_simulation_data() noexcept{
        return simulation_data;
    }
    const std::vector<BtorBitVectorPtr>& get_simulation_data() const noexcept {
        return simulation_data;
    }

    size_t hash() const {
        return hash(simulation_data);
    }

    static size_t hash(const std::vector<BtorBitVectorPtr>& data) {
        if (data.empty()) {
            return 0;
        }

        size_t hash_val = 0;
        for(const auto & v : data) {
            auto clean_val = btor_bv_to_string(*v);
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
    
    auto& sim_data = nd.get_simulation_data();
    
    if(op.prim_op == PrimOp::Not) {
        auto current_val = btor_bv_not(btor_child_1);
        nd.get_simulation_data().push_back(btor_bv_not(btor_child_1));
    }
    else if(op.prim_op == PrimOp::BVNot) {
        auto current_val = btor_bv_not(btor_child_1);
        nd.get_simulation_data().push_back(btor_bv_not(btor_child_1));
    }
    else if(op.prim_op == PrimOp::Extract) {
        auto high = op.idx0;
        auto low = op.idx1;
        assert(high >= low);
        auto current_val = btor_bv_slice(btor_child_1, high, low);
        assert(current_val->width == high - low + 1);
        nd.get_simulation_data().push_back(btor_bv_slice(btor_child_1, high, low));
    }
    else if(op.prim_op == PrimOp::Zero_Extend) {
        auto current_val = btor_bv_uext(btor_child_1, op.idx0);
        nd.get_simulation_data().push_back(btor_bv_uext(btor_child_1, op.idx0));
    }
    else if(op.prim_op == PrimOp::Sign_Extend) {
        auto current_val = btor_bv_sext(btor_child_1, op.idx0);
        nd.get_simulation_data().push_back(btor_bv_sext(btor_child_1, op.idx0));
    }
    else if(op.prim_op == PrimOp::BVNeg) {
        sim_data.push_back(btor_bv_neg(btor_child_1));
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
    auto& sim_data = nd.get_simulation_data();
    
    if(op.prim_op == PrimOp::BVAdd) {
        auto result = btor_bv_add(btor_child_1, btor_child_2);
        sim_data.push_back(btor_bv_add(btor_child_1, btor_child_2));
    } 
    else if(op.prim_op == PrimOp::BVAnd) {
        sim_data.push_back(btor_bv_add(btor_child_1, btor_child_2));
        auto result = btor_bv_and(btor_child_1, btor_child_2);
    }
    else if(op.prim_op == PrimOp::And) {
        sim_data.push_back(btor_bv_and(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::Concat) {
        sim_data.push_back(btor_bv_concat(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::Equal) {
        sim_data.push_back(std::move(btor_bv_eq(btor_child_1, btor_child_2)));
    }
    else if(op.prim_op == PrimOp::Xor || op.prim_op == PrimOp::BVXor) {
        sim_data.push_back(btor_bv_xor(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::Or || op.prim_op == PrimOp::BVOr) {
        sim_data.push_back(btor_bv_or(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVMul) {
        sim_data.push_back(btor_bv_add(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVComp) {
        auto current_val = btor_bv_compare(btor_child_1, btor_child_2);
        auto current_val_bv = btor_bv_int64_to_bv(current_val, 1);
        nd.get_simulation_data().push_back(btor_bv_int64_to_bv(btor_bv_compare(btor_child_1, btor_child_2),1));
    }
    else if(op.prim_op == PrimOp::Distinct) {
        sim_data.push_back(btor_bv_ne(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVUdiv) {
        sim_data.push_back(btor_bv_udiv(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVSub) {
        sim_data.push_back(btor_bv_sub(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVUlt) {
        sim_data.push_back(btor_bv_ult(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVUle) {
        sim_data.push_back(btor_bv_ulte(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVUgt) {
        sim_data.push_back(btor_bv_ugt(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVUge) {
        sim_data.push_back(btor_bv_ugte(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVSlt) {
        sim_data.push_back(btor_bv_slt(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVSle) {
        sim_data.push_back(btor_bv_slte(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVSgt) {
        sim_data.push_back(btor_bv_sgt(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVSge) {
        sim_data.push_back(btor_bv_sgte(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVNand) {
        sim_data.push_back(btor_bv_nand(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVNor) {
        sim_data.push_back(btor_bv_nor(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVXnor) {
        sim_data.push_back(btor_bv_xnor(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVUrem) {
        sim_data.push_back(btor_bv_urem(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVSdiv) {
        sim_data.push_back(btor_bv_sdiv(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVSrem) {
        sim_data.push_back(btor_bv_srem(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVLshr) {
        sim_data.push_back(btor_bv_srl(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVAshr) {
        sim_data.push_back(btor_bv_sra(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::BVShl) {
        sim_data.push_back(btor_bv_sll(btor_child_1, btor_child_2));
    }
    else if(op.prim_op == PrimOp::Implies) {
        sim_data.push_back(btor_bv_implies(btor_child_1, btor_child_2));
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
        auto result = btor_bv_ite(btor_child_1, btor_child_2, btor_child_3);
        if(!result){
            std::cerr << "Warning: btor_bv_ite returned nullptr.\n";
            // 可选：抛出异常或跳过
            throw std::runtime_error("Null result in btor_bv_operation_3children");
        }
        nd.get_simulation_data().push_back(btor_bv_ite(btor_child_1, btor_child_2, btor_child_3));
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
        btor_bv_operation_1child(op_type, *bv_child, out);
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

            auto index_str = std::string(btor_bv_to_string(*sim_data_index[i]));
            const auto & val_str = all_luts.at(array_var).at(index_str);
            // cout << "index: " << index_str << ", value: " << val_str << endl;
            auto val = btor_bv_char_to_bv(val_str.data());
            nd.get_simulation_data().push_back(btor_bv_char_to_bv(val_str.data()));
        }

    }else { // for other bit-vector operations
        const auto& child_1 = children[0];
        const auto& child_2 = children[1];


        // If substitution happened, we must get the resolved node and use its simulation data
        const auto& sim_data_1 = node_data_map.at(child_1).get_simulation_data();
        const auto& sim_data_2 = node_data_map.at(child_2).get_simulation_data();
        
        //debug
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
        

        // Perform the operation on the simulation data
        for (size_t i = 0; i < num_iterations; ++i) {
            const auto& btor_child_1 = sim_data_1[i];
            const auto& btor_child_2 = sim_data_2[i];
            btor_bv_operation_2children(op_type, *btor_child_1, *btor_child_2, nd);
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
                                       bool debug = false)
{
    const auto& sim_data_1 = node_data_map.at(children[0]).get_simulation_data();
    const auto& sim_data_2 = node_data_map.at(children[1]).get_simulation_data();
    const auto& sim_data_3 = node_data_map.at(children[2]).get_simulation_data();

    //debug
    assert(sim_data_1.size() == static_cast<size_t>(num_iterations));
    assert(sim_data_2.size() == static_cast<size_t>(num_iterations));
    assert(sim_data_3.size() == static_cast<size_t>(num_iterations));
    

    for (size_t i = 0; i < num_iterations; i++) {
        // Retrieve the bit-vector data for each child at the current iteration
        auto& btor_child_1 = *sim_data_1[i];
        auto& btor_child_2 = *sim_data_2[i];
        auto& btor_child_3 = *sim_data_3[i];

        if (!sim_data_1[i] || !sim_data_2[i] || !sim_data_3[i]) {
            std::cerr << "[Simulation Error] Null pointer detected at iteration " << i << "\n";
            throw std::runtime_error("Null simulation data pointer");
        }
        

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

void reduce_unsat_core_to_fixedpoint(
    smt::UnorderedTermSet & core_inout,
    const smt::SmtSolver & reducer_,
    Result& r) 
{

    while(true) {
        r = reducer_->check_sat_assuming_set(core_inout);
        assert(r.is_unsat());

        smt::UnorderedTermSet core_out;
        reducer_->get_unsat_assumptions(core_out);
        if (core_inout.size() == core_out.size()) {
            break; // fixed point is reached
        }
        assert(core_out.size() < core_inout.size());
        core_inout.swap(core_out);  // namely, core_inout = core_out,  but no need to copy
    }
} // end of reduce_unsat_core_to_fixedpoint

void remove_and_move_to_next(smt::TermList & pred_set, smt::TermList::iterator & pred_pos,
    const smt::UnorderedTermSet & unsatcore) {

    auto pred_iter = pred_set.begin(); // pred_pos;
    auto pred_pos_new = pred_set.begin();

    bool reached = false;
    bool next_pos_found = false;

    while( pred_iter != pred_set.end() ) {

        if (pred_iter == pred_pos) {
            assert (!reached);
            reached = true;
        }
        
        if (unsatcore.find(*pred_iter) == unsatcore.end()) {
            assert (reached);
            pred_iter = pred_set.erase(pred_iter);
        } else {
            if (reached && ! next_pos_found) {
                pred_pos_new = pred_iter;
                next_pos_found = true;
            }
            ++ pred_iter;
        }
    } // end of while

    assert(reached);
    if (! next_pos_found) {
        assert (pred_iter == pred_set.end());
        pred_pos_new = pred_iter;
    }
    pred_pos = pred_pos_new;
} // end of remove_and_move_to_next

smt::Term get_first_unreducible_term (
    smt::TermList & assumption_list,
    const smt::SmtSolver & reducer_,
    Result & r) {
  
    r = reducer_->check_sat_assuming_list(assumption_list);
    assert(r.is_unsat());
    auto to_remove_pos = assumption_list.begin();

    while(to_remove_pos != assumption_list.end()) {
        smt::Term term_to_remove = *to_remove_pos;
        auto pos_after = assumption_list.erase(to_remove_pos);
        r = reducer_->check_sat_assuming_list(assumption_list);
        to_remove_pos = assumption_list.insert(pos_after, term_to_remove);
        
        if (r.is_sat()) {
            return term_to_remove;
        } else { // if unsat, we can remove
            smt::UnorderedTermSet core_set;
            reducer_->get_unsat_assumptions(core_set);
            // below function will update assumption_list and to_remove_pos
            remove_and_move_to_next(assumption_list, to_remove_pos, core_set);
        }
    } // end of while
} // end of reduce_unsat_core_linear

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


inline bool has_simulation_data(const Term& t, const std::unordered_map<Term, NodeData>& node_data_map) {
    auto it = node_data_map.find(t);
    return it != node_data_map.end() && !it->second.get_simulation_data().empty();
}


void simulate_constant_node(const smt::Term& current, 
                            int & num_iterations, 
                            std::unordered_map<Term, NodeData>& node_data_map) 
{
    if (has_simulation_data(current, node_data_map)) return; // skip if already exists

    NodeData nd(current);
    auto & sim_vec = nd.get_simulation_data(); // 引用，直接操作 vector<BtorBitVectorPtr>
    
    if (current->get_sort()->get_sort_kind() == BOOL) {
        std::string bitval = (current->to_string() == "true") ? "1" : "0";
        for (int i = 0; i < num_iterations; ++i) {
            sim_vec.push_back(btor_bv_char_to_bv(bitval.c_str()));
        }
    } else {
        std::string val = current->to_string().substr(2);
        for (int i = 0; i < num_iterations; ++i) {
            sim_vec.push_back(btor_bv_char_to_bv(val.c_str()));
        }
    }

    node_data_map[current] = std::move(nd);
    assert(node_data_map[current].get_simulation_data().size() == num_iterations);
}




struct TryFindResult {
    bool found;
    Term term_eq;
    TermVec terms_for_solving;
};

// TryFindResult try_find_equiv_term(const Term & cnode,
//                                   const uint32_t & current_hash,
//                                   const NodeData & sim_data,
//                                   int & num_iterations,
//                                   const std::unordered_map<uint32_t, TermVec> & hash_term_map,
//                                   const std::unordered_map<Term, NodeData> & node_data_map,
//                                   const std::unordered_map<Term, Term> & substitution_map,
//                                   bool & debug) {
//     TryFindResult result {false, nullptr, {}};

//     if (hash_term_map.find(current_hash) == hash_term_map.end()) return result;
//     const auto & terms_to_check = hash_term_map.at(current_hash);
//     const auto & sim_data_vec = sim_data.get_simulation_data();
//     size_t size = terms_to_check.size();
    

//     //partial vector to minimize the number of terms to check
//     smt::TermVec filtered_terms;
//     std::mt19937 rng(std::random_device{}());

//     if (size <= 4) {
//         filtered_terms = terms_to_check;
//     }
//     else if (size <= 10) {
//         if (size >= 6) {
//             filtered_terms.insert(filtered_terms.end(), terms_to_check.begin(), terms_to_check.begin() + 3);
//             filtered_terms.insert(filtered_terms.end(), terms_to_check.end() - 3, terms_to_check.end());
//         } else {
//             size_t first = std::min(size_t(2), size);
//             size_t last = std::min(size_t(2), size - first);
//             filtered_terms.insert(filtered_terms.end(), terms_to_check.begin(), terms_to_check.begin() + first);
//             filtered_terms.insert(filtered_terms.end(), terms_to_check.end() - last, terms_to_check.end());
//         }
//     }
//     else {
//         size_t prefix_count = 0, suffix_count = 0, max_middle_sample = 0, cap = 20;

//         if (size <= 30) {
//             prefix_count = std::min(size_t(4), size);
//             suffix_count = std::min(size_t(4), size - prefix_count);
//             max_middle_sample = std::min(size - prefix_count - suffix_count, size_t(4));
//             cap = 12;
//         } else if (size <= 50) {
//             prefix_count = std::min(size_t(5), size);
//             suffix_count = std::min(size_t(5), size - prefix_count);
//             max_middle_sample = std::min(size - prefix_count - suffix_count, size_t(5));
//             cap = 15;
//         } else if (size <= 100) {
//             prefix_count = std::min(size_t(5), size);
//             suffix_count = std::min(size_t(5), size - prefix_count);
//             max_middle_sample = std::min(size_t(8), size - prefix_count - suffix_count);
//             cap = 18;
//         } else {
//             prefix_count = std::min(size_t(5), size);
//             suffix_count = std::min(size_t(5), size - prefix_count);
//             max_middle_sample = std::min(size_t(10), size - prefix_count - suffix_count);
//             cap = 20;
//         }

//         smt::TermVec prefix, suffix, middle_sample;

//         prefix.insert(prefix.end(), terms_to_check.begin(), terms_to_check.begin() + prefix_count);
//         suffix.insert(suffix.end(), terms_to_check.end() - suffix_count, terms_to_check.end());

//         auto middle_start = terms_to_check.begin() + prefix_count;
//         auto middle_end   = terms_to_check.end() - suffix_count;
//         smt::TermVec middle(middle_start, middle_end);

//         std::sample(middle.begin(), middle.end(),
//                     std::back_inserter(middle_sample),
//                     max_middle_sample, rng);

//         filtered_terms.reserve(prefix.size() + middle_sample.size() + suffix.size());
//         filtered_terms.insert(filtered_terms.end(), prefix.begin(), prefix.end());
//         filtered_terms.insert(filtered_terms.end(), middle_sample.begin(), middle_sample.end());
//         filtered_terms.insert(filtered_terms.end(), suffix.begin(), suffix.end());

//         if (filtered_terms.size() > cap) {
//             filtered_terms.resize(cap);
//         }
//     }

//     for (const auto & t : filtered_terms) {
//         if (t == cnode) {
//             result.found = true;
//             result.term_eq = t;
//             return result;
//         }
        
//         if (t->get_sort() != cnode->get_sort()) {
//             continue;
//         }

//         if (node_data_map.find(t) == node_data_map.end()) {
//             std::ostringstream oss;
//             oss << "[Missing Data] Simulation data not found in node_data_map for term:\n"
//                 << "  - Term: " << t;
//             std::cerr << oss.str() << std::endl;
//             continue;
//         }
        
//         const auto & existing_sim_data = node_data_map.at(t).get_simulation_data();
//         bool match = true;
//         for (int i = 0; i < num_iterations; ++i) {
//             if (btor_bv_compare(*existing_sim_data[i], *sim_data_vec[i]) != 0) {
//                 match = false;
//                 break;
//             }
//         }
//         if (match) {
//             result.terms_for_solving.push_back(t);
//         }
//     }

//     return result;
// }

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

    // 不使用随机过程，直接顺序遍历所有 terms_to_check
    for (const auto & t : terms_to_check) {
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
            if (btor_bv_compare(*existing_sim_data[i], *sim_data_vec[i]) != 0) {
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
                
                for (int i = 0; i < num_iterations; ++i){
                    auto current_bv = btor_bv_char_to_bv(bitval.c_str());
                    node_data_map[current].get_simulation_data().push_back(std::move(current_bv));
                }
            } else {
                std::string current_str = current->to_string().substr(2);
                
                if(node_data_map[current].get_simulation_data().empty()){
                    for (int i = 0; i < num_iterations; ++i) {
                        auto current_bv = btor_bv_char_to_bv(current_str.data());
                        node_data_map[current].get_simulation_data().push_back(std::move(current_bv));
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
                sim_vec.push_back(std::move(bv));
        } else if (term->is_symbolic_const() && term->get_op().is_null()) {
            Term val = solver->get_value(term);
            std::string val_str = (term->get_sort()->get_sort_kind() == BOOL)
                ? ((val->to_string() == "true") ? "1" : "0")
                : val->to_string().substr(2);
            sim_vec.push_back(btor_bv_char_to_bv(val_str.c_str()));
        } else {
            TermVec children(term->begin(), term->end());
            TermVec substituted;
            children_substitution(children, substituted, substitution_map);
            NodeData temp_sim;
            int one_iter = 1;
            compute_simulation(substituted, one_iter, term->get_op(), node_data_map, all_luts, temp_sim);
            sim_vec.push_back(std::move(temp_sim.get_simulation_data().front()));
        }

        if (sim_vec.size() != (size_t)num_iterations) {
            std::cerr << "[FATAL] Post-fill simulation_data size mismatch for term: "
                      << term->to_string() << " size: " << sim_vec.size() << " vs expected: " << num_iterations << std::endl;
            exit(EXIT_FAILURE);
        }
    }
}
