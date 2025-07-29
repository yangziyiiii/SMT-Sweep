#include "./sweeping.h"
#include "smt-switch/bitwuzla_factory.h"
#include <fstream>
#include <iostream>
#include <unordered_map>
#include <vector>
#include <string>

void read_simulation_inputs(const std::string & load_file_path, 
                           const UnorderedTermSet& free_symbols,
                           std::vector<TermVec> & formulas_per_iter,
                           SmtSolver& solver
){
    std::ifstream infile(load_file_path);
    if (!infile.is_open()) {
        std::cerr << "[ERROR] Cannot open simulation input file: " << load_file_path << std::endl;
        return;
    }

    std::unordered_map<std::string, Term> term_lookup;
    for (const auto & term : free_symbols) {
        std::string name = term->to_string();
        if (name.size() >= 2 && name.front() == '|' && name.back() == '|')
            name = name.substr(1, name.size() - 2);
        term_lookup[name] = term;
    }
    

    std::regex header_re(R"(\[SIMULATION\s+ITERATION\s+(\d+)\])",std::regex::icase);
    std::string line;
    TermVec  *curr_vec = nullptr;              // 当前迭代对应的 TermVec

    while (std::getline(infile, line)) {
        if (line.empty()) continue;

        // 1. 先判断是否为新的迭代头
        std::smatch m;
        if (std::regex_match(line, m, header_re)) {
            formulas_per_iter.emplace_back();  // 创建新分组
            curr_vec = &formulas_per_iter.back();
            continue;
        }

        // 没遇到迭代头但 curr_vec 仍为空 → 跳过前导杂项
        if (!curr_vec) continue;

        // 2. 正常解析 “var = value” 行
        size_t pos = line.find(" = ");
        if (pos == std::string::npos) continue;

        std::string var  = line.substr(0, pos);
        std::string bits = line.substr(pos + 3);   // 取右侧

        if (!bits.empty() && bits.rfind("#b", 0) == 0)
            bits.erase(0, 2);                      // 去掉前缀 #b

        auto it = term_lookup.find(var);
        if (it == term_lookup.end()) continue;     // 非自由符号 → 忽略

        Term  lhs  = it->second;
        Sort  sort = lhs->get_sort();
        Term  rhs  = solver->make_term(bits, sort, 2);
        Term  eq   = solver->make_term(Equal, lhs, rhs);

        // std::cout << "[Simulation] (iter "
        //           << formulas_per_iter.size()    // 当前迭代编号
        //           << ") " << lhs->to_string()
        //           << " = " << rhs->to_string()
        //           << std::endl;

        curr_vec->push_back(eq);
    }
}


inline TermVec flatten_and_constraints(const TermVec & constraints) {
    TermVec atoms;
    vector<Term> stack(constraints.begin(), constraints.end());

    while (!stack.empty()) {
        Term cur = stack.back();
        stack.pop_back();

        if (cur->get_op() == And) {
            for (auto it = cur->begin(); it != cur->end(); ++it)
                stack.push_back(*it);
        } else atoms.push_back(cur);
    }
    return atoms;
}



int main(int argc, char* argv[]) {
    if (argc < 4) {
        std::cerr << "Usage: " << argv[0] << " <BTOR2_FILE_PATH> <INPUT_TXT_PATH> <BOUND>" << std::endl;
        return 1;
    }

    std::string btor2_file = argv[1];
    std::string input_txt_file = argv[2];
    int bound = std::stoi(argv[3]);

    SmtSolver solver = BitwuzlaSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");

    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(btor2_file, sts);

    SymbolicSimulator sim(sts, solver);

    std::ifstream infile(input_txt_file);
    if (!infile.is_open()) {
        std::cerr << "[ERROR] Cannot open input file: " << input_txt_file << std::endl;
        return 1;
    }

    const auto & propvec = sts.prop();
    if (propvec.empty()) {
        std::cout << "No property to check!" << std::endl;
        return 1;
    }
    auto prop = and_vec(propvec, solver);

    sim.init();
    sim.set_input({},{});
    

    std::vector<TermVec> iteration_formulas;
    

    for (auto i = 1; i<=bound; ++i) {
        sim.sim_one_step();
        sim.set_input({},{});
    }


    TermVec constraints = sim.all_assumptions();
    std::cout << "[Simulation] constraints: " << constraints.size() << std::endl;
    auto root = sim.interpret_state_expr_on_curr_frame(prop, false);
    UnorderedTermSet free_symbols;
    smt::get_free_symbols(root, free_symbols);
    read_simulation_inputs(input_txt_file, free_symbols, iteration_formulas, solver);
    int total = 0;
    int success = 0;

    auto atoms = flatten_and_constraints(constraints);

    for(auto c : iteration_formulas) {
        int sat_this = 0;
        solver->push();
        for (const auto& eq : c) {
            solver->assert_formula(eq);
        }
        for(const auto con : constraints) {
            Result r = solver->check_sat_assuming({con});
            if(r.is_sat()){
                sat_this ++;
                total ++;
                success ++;
            } else {
                total ++;
            }
        }
        std::cout << "[Rate] " << sat_this << " of " << constraints.size() << std::endl;
        solver->pop();
    }

    std::cout << "[Simulation] Successful checks: " << total << ", success :" << success << std::endl;
    return 0;
}
