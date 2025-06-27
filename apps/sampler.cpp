#include <chrono>
#include "smt-switch/bitwuzla_factory.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/utils.h"
#include <gmp.h>
#include <gmpxx.h>
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



// RAII wrapper for GMP random state
class GmpRandStateGuard
{
    gmp_randstate_t state;

    public:
    GmpRandStateGuard()
    {
        gmp_randinit_default(state);
        gmp_randseed_ui(state, 42);
    }

    ~GmpRandStateGuard() { gmp_randclear(state); }

    void random_input(mpz_t & rand_num, int num)
    {
        mpz_init2(rand_num, num);
        mpz_urandomb(rand_num, state, num);
    }

    // operator gmp_randstate_t &() { return state; }
    
};
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
    auto start = std::chrono::steady_clock::now();

    if (argc != 3) {
        std::cerr << "Usage: " << argv[0] << " <file.smt2> <num_samples>\n";
        return 1;
    }
    std::string smt_file = argv[1];
    int num_samples = std::stoi(argv[2]);

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

    // ============== find free symbols ==============
    UnorderedTermSet inputs_set;
    for (const auto & a : reader.captured_assertions)
        get_free_symbols(a, inputs_set);
    TermVec inputs(inputs_set.begin(), inputs_set.end());
    for(const auto & t : inputs) {
        std::cout << "Input: " << t->to_string() << std::endl;
    }

    // ============== find constraints ===========
    for (size_t i = 0; i < reader.captured_assertions.size(); ++i) {
        // cout << "Assertion " << i << ":" << endl;
        // print_ast(reader.captured_assertions[i]);
        constraints.push_back(reader.captured_assertions[i]);
        solver->assert_formula(reader.captured_assertions[i]);
    }
    cout << "constraint size: " << constraints.size() << endl;


    cout << "== step1: random simulation ==" << endl;
    GmpRandStateGuard rand_guard;
    std::size_t collected = 0;          // 成功样本计数
    std::size_t trial_id  = 0;          // 总尝试计数（含失败）

    while (collected < static_cast<std::size_t>(num_samples)) {
        ++ trial_id;
        solver->push();
        unordered_map<Term, string> val;
        TermVec assumptions;

        for(const auto input : inputs){
            auto width = input->get_sort()->get_width();
            mpz_t input_mpz;
            rand_guard.random_input(input_mpz, width);
            std::unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(nullptr, 2, input_mpz), free);
            mpz_clear(input_mpz);
            val[input] = std::string(input_str.get());

            Sort bv_sort = solver->make_sort(BV, width);
            Term input_random_val = solver->make_term(string(input_str.get()), bv_sort, 2);
            Term eq = solver->make_term(Equal, input, input_random_val);
            std::cout << input->to_string() << ": " << input_random_val << std::endl;
            assumptions.push_back(eq);
        }

        Result r = solver->check_sat_assuming(assumptions);
        bool sat_ok = r.is_sat();

        if (!sat_ok) {
            UnorderedTermSet core;
            solver->get_unsat_assumptions(core);
            reduce_unsat_core_to_fixedpoint(core, solver, r);
            TermList corelist(core.begin(), core.end());

            auto erase_core_term = [](TermVec &v, const Term &t) {
                v.erase(remove_if(v.begin(), v.end(),
                                [&](const Term &x){ return x == t; }), v.end());
            };

            while (!corelist.empty())
            {
                Term term_to_reduce = get_first_unreducible_term(corelist, solver, r);
                cout << "before size: " << assumptions.size() << endl;
                erase_core_term(assumptions, term_to_reduce);
                cout << "after size: " << assumptions.size() << endl;

                solver->pop(); 
                solver->push();
                r = solver->check_sat_assuming(assumptions);
                if (r.is_sat()) { sat_ok = true; break; }

                core.clear();
                solver->get_unsat_assumptions(core);
                reduce_unsat_core_to_fixedpoint(core, solver, r);
                corelist.assign(core.begin(), core.end());
            }
        }

        if (sat_ok)
        {
            out << "# sample " << collected << "  (trial " << trial_id << ")\n";
            for (const auto &inp : inputs)
            {
                string bits;
                if (auto it = val.find(inp); it != val.end())
                    bits = it->second;                          // 已有随机值
                else
                {                                              // 需从模型获取
                    Term c = solver->get_value(inp);
                    bits   = c->to_string();               // 使用前述通用函数
                }
                out << inp->to_string() << " = " << bits << '\n';
            }
            out << '\n';
            ++collected;                                       // 成功样本 +1
        }
        else {
            cerr << "[WARN] trial " << trial_id
                 << " 仍无法取得 SAT，放弃该样本\n";
        }
        solver->pop(); 
    }


    out << "rate: " << collected / trial_id << '\n';
    out.close();
    
    auto end = std::chrono::steady_clock::now();
    out << "Total time: "
        << std::chrono::duration_cast<std::chrono::milliseconds>(end - start).count() / 1000
        << " s" << std::endl;
    return 0;
}