#include <chrono>
#include "smt-switch/bitwuzla_factory.h"
#include "smt-switch/smtlib_reader.h"
#include <fstream>
#include <bitset>

using namespace smt;
using namespace std;

class AssertCapturingReader : public smt::SmtLibReader {
public:
    vector<Term> captured_assertions;
    
    AssertCapturingReader(smt::SmtSolver& solver) : SmtLibReader(solver) {}
    
    void assert_formula(const Term& assertion) override {
        captured_assertions.push_back(assertion);
        SmtLibReader::assert_formula(assertion);
    }
};

void print_ast(const Term& term, int depth = 0) {
    string indent(depth * 2, ' ');
    cout << indent << "Term: " << term->to_string() << endl;
    // cout << indent << "Sort: " << term->get_sort()->to_string() << endl;
    // cout << indent << "Op: " << term->get_op().to_string() << endl;
    
    // // Print children
    // if (term->begin() != term->end()) {
    //     cout << indent << "Children:" << endl;
    //     for (auto it = term->begin(); it != term->end(); ++it) {
    //         print_ast(*it, depth + 1);
    //     }
    // }
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

int main(int argc, char* argv[]) {
    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " <file.smt2>\n";
        return 1;
    }
    auto start = std::chrono::steady_clock::now();

    std::string smt_file = argv[1];
    int bound = std::stoi(argv[2]);

    std::ofstream out("stimuli_all.txt", std::ios::out | std::ios::trunc);
    if (!out.is_open()) {
        std::cerr << "Error: Unable to open output file." << std::endl;
        return 1;
    }

    SmtSolver solver = BitwuzlaSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    AssertCapturingReader reader(solver);
    reader.parse(smt_file);

    TermVec constraints;
    TermVec inputs;

    cout << "=== Lookup input ===" << endl;
    for (int i = 0; i <= 13; ++i) {
        auto input = reader.lookup_symbol("input!" + std::to_string(i)); //FIXME
        inputs.push_back(input);
    }

    constexpr int NUM_INPUTS = 14;
    constexpr int BIT_WIDTH = 32;
    std::vector<std::vector<std::bitset<2>>> coverage(NUM_INPUTS, std::vector<std::bitset<2>>(BIT_WIDTH));

    auto erase_core_term = [](smt::TermVec &v, const smt::Term &term) -> std::size_t {
        const auto old_sz = v.size();
        v.erase(std::remove_if(v.begin(), v.end(),
                            [&](const smt::Term &t) { return t == term; }),
                v.end());
        return old_sz - v.size();
    };

    cout << "=== Assertions AST ===" << endl;
    for (size_t i = 0; i < reader.captured_assertions.size(); ++i) {
        // cout << "Assertion " << i << ":" << endl;
        print_ast(reader.captured_assertions[i]);
        constraints.push_back(reader.captured_assertions[i]);
        solver->assert_formula(reader.captured_assertions[i]);
    }

    cout << "=== Check SAT ===" << endl;
    int stimuli_count = 0;
    TermVec current_inputs = inputs;
    while (stimuli_count < bound) {
        out << "=== Trial " << stimuli_count << " ===" << std::endl;

        Result res = solver->check_sat_assuming(current_inputs);
        out << "Result: " << res.to_string() << std::endl;

        if (res.is_sat()) {
            for (const auto &input : inputs) {
                Term val = solver->get_value(input);
                out << input->to_string() << " = " << val->to_string() << std::endl;
            }
            out << std::endl;
            ++stimuli_count;
            TermVec blocking_literals;
            for (const auto &input : inputs) {
                Term val = solver->get_value(input);
                Term lit = solver->make_term(Equal, input, val);
                blocking_literals.push_back(lit);
            }
            Term block = solver->make_term(Not, solver->make_term(And, blocking_literals));
            solver->assert_formula(block);
        } else if (res.is_unsat()) {
            UnorderedTermSet core;
            solver->get_unsat_assumptions(core);
            reduce_unsat_core_to_fixedpoint(core, solver, res);

            smt::TermList corelist(core.begin(), core.end());
            auto term_to_remove = get_first_unreducible_term(corelist, solver, res);
            if (erase_core_term(current_inputs, term_to_remove) == 0) {
                out << "Error: Failed to reduce unsat core." << std::endl;
                break;
            }
        } else {
            out << "Unknown solver result. Abort." << std::endl;
            break;
        }
    }

    out << "Total time: "
        << std::chrono::duration_cast<std::chrono::milliseconds>(
               std::chrono::steady_clock::now() - start)
               .count()
        << " ms" << std::endl;

    // ===== Coverage Evaluation =====
    auto coverage_start = std::chrono::steady_clock::now();
    int total_bits = NUM_INPUTS * BIT_WIDTH;
    int covered_bits = 0;

    for (int i = 0; i < NUM_INPUTS; ++i) {
        for (int j = 0; j < BIT_WIDTH; ++j) {
            if (coverage[i][j] == std::bitset<2>("11")) {
                ++covered_bits;
            }
        }
    }

    double percent = (100.0 * covered_bits) / total_bits;
    out << "Coverage: " << covered_bits << "/" << total_bits << " bits (" << percent << "%)" << std::endl;

    auto coverage_end = std::chrono::steady_clock::now();
    out << "Coverage evaluation time: "
        << std::chrono::duration_cast<std::chrono::milliseconds>(coverage_end - coverage_start).count()
        << " ms" << std::endl;


    out.close();
    
    return 0;
}