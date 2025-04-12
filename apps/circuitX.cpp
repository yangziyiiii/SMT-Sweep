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
#include <iostream>

using namespace smt;
using namespace std;
using namespace wasim;

int main() {
    // Create SMT solver with proper configuration
    SmtSolver s = BitwuzlaSolverFactory::create(false);
    s->set_logic("QF_BV");
    s->set_opt("incremental", "true");
    s->set_opt("produce-models", "true");
    s->set_opt("produce-unsat-assumptions", "true");

    // Create transition system and parse BTOR2 file
    TransitionSystem ts(s);
    BTOR2Encoder btor_parser("../design/case02_rewrite.btor2", ts);

    // Get the input variables L and S
    Term L = ts.lookup("L0");
    Term S = ts.lookup("S0");
    Term D = ts.lookup("D");

    // Get all state variables
    UnorderedTermSet state_vars;
    for (const auto & sv : ts.statevars()) {
        state_vars.insert(sv);
    }

    // Create a second copy of S and state variables for comparison
    Term S2 = s->make_symbol("S2", S->get_sort());
    UnorderedTermMap state_copies;
    for (const auto & sv : state_vars) {
        state_copies[sv] = s->make_symbol(sv->to_string() + "_2", sv->get_sort());
    }

    // Add state copies to the substitution map
    UnorderedTermMap subst;
    subst[S] = S2;
    for (const auto & p : state_copies) {
        subst[p.first] = p.second;
    }

    // Create second copy of the circuit output using S2 and state copies
    Term D2 = s->substitute(D, subst);

    // Add constraint: S ≠ S2 (to make sure we're testing different S values)
    s->assert_formula(s->make_term(Distinct, S, S2));

    // Assert initial state constraints for both copies
    for (const auto & init : ts.init()) {
        s->assert_formula(init);
        s->assert_formula(s->substitute(init, state_copies));
    }

    // Assert transition relation for both copies
    for (const auto & trans : ts.trans()) {
        s->assert_formula(trans);
        s->assert_formula(s->substitute(trans, state_copies));
    }

    // The condition: D1 and D2 must be equal (output should be independent of S)
    Term condition = s->make_term(Equal, D, D2);
    s->assert_formula(condition);

    Result r = s->check_sat();

    if (r.is_sat()) {
        cout << "Solution found! L value that makes D independent of S:" << endl;
        cout << "L = " << s->get_value(L)->to_string() << endl;
        cout << "Verification with two different S values:" << endl;
        cout << "S1 = " << s->get_value(S)->to_string() << endl;
        cout << "S2 = " << s->get_value(S2)->to_string() << endl;
        cout << "D1 = " << s->get_value(D)->to_string() << " (should equal D2)" << endl;
        cout << "D2 = " << s->get_value(D2)->to_string() << " (should equal D1)" << endl;

        // Print state values for both copies
        cout << "\nState values for first copy:" << endl;
        for (const auto & sv : state_vars) {
            cout << sv->to_string() << " = " << s->get_value(sv)->to_string() << endl;
        }
        cout << "\nState values for second copy:" << endl;
        for (const auto & p : state_copies) {
            cout << p.first->to_string() << " = " << s->get_value(p.second)->to_string() << endl;
        }

        // Additional verification: try all possible S values for the found L
        Term L_val = s->get_value(L);
        s->push();
        s->assert_formula(s->make_term(Equal, L, L_val));

        cout << "\nVerifying that this L value works for all S values..." << endl;

        // Try to find any S1, S2 that give different outputs
        Term different_outputs = s->make_term(Distinct, D, D2);
        s->assert_formula(different_outputs);

        Result verify = s->check_sat();
        if (verify.is_unsat()) {
            cout << "Verified: This L value makes D independent of S for all possible S values!" << endl;
        } else {
            cout << "Error: Found counter-example where outputs differ:" << endl;
            cout << "S1 = " << s->get_value(S)->to_string() << endl;
            cout << "S2 = " << s->get_value(S2)->to_string() << endl;
            cout << "D1 = " << s->get_value(D)->to_string() << endl;
            cout << "D2 = " << s->get_value(D2)->to_string() << endl;

            cout << "\nState values in counter-example:" << endl;
            for (const auto & sv : state_vars) {
                cout << sv->to_string() << " = " << s->get_value(sv)->to_string() << endl;
            }
            for (const auto & p : state_copies) {
                cout << p.first->to_string() << " = " << s->get_value(p.second)->to_string() << endl;
            }
        }
        s->pop();
    } else {
        cout << "No solution exists: D always depends on S for all L values." << endl;
    }

    return 0;
}