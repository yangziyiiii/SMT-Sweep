
#include <ostream>
#include <utility>
#include <chrono>
#include <numeric>
#include <algorithm>
#include <random>
#include <cassert>
#include <unordered_map>
#include <vector>
#include <string>

#include "smt-switch/bitwuzla_factory.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/utils.h"
#include "framework/ts.h"
#include "framework/symsim.h"
#include "frontend/btor2_encoder.h"
#include "config/testpath.h"

#include <gmp.h>
#include <gmpxx.h>
#include <fstream>

using namespace smt;
using namespace std;
using namespace wasim;

inline TermVec flatten_and_constraints(const TermVec & constraints) {
    TermVec atoms;
    vector<Term> stack(constraints.begin(), constraints.end());

    while (!stack.empty()) {
        Term cur = stack.back();
        stack.pop_back();

        if (cur->get_op() == And) {
            for (auto it = cur->begin(); it != cur->end(); ++it)
                stack.push_back(*it);
        } else{
            atoms.push_back(cur);
        }
    }
    return atoms;
}

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
    GmpRandStateGuard(const GmpRandStateGuard&) = delete;
    GmpRandStateGuard& operator=(const GmpRandStateGuard&) = delete;

    void random_input(mpz_t & rand_num, int num)
    {
        mpz_init2(rand_num, num);
        mpz_urandomb(rand_num, state, num);
    }

    // operator gmp_randstate_t &() { return state; }
    
};



smt::TermVec random_simulation(
    const UnorderedTermSet & inputs,
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
                assumptions.push_back(eq);
                break;
            }
            case BOOL: {
                // For boolean sorts, we randomly choose true or false
                bool value = rand() % 2;
                Term input_random_val = solver->make_term(value ? 1 : 0);
                Term eq = solver->make_term(Equal, in, input_random_val);
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


TermVec rebuild_assumptions(const unordered_map<Term, string> & model, const SmtSolver & solver) {
    TermVec assum;
    for (const auto & [sym, val_str] : model) {
        Sort s = sym->get_sort();
        Term const_term = solver->make_term(val_str, s, 2);
        assum.push_back(solver->make_term(Equal, sym, const_term));
    }
    return assum;
}


inline size_t evaluate_energy(const TermVec & constraints,
                              const TermVec & assumptions,
                              const SmtSolver & solver)
{
    solver->push();

    for (Term eq : assumptions) 
        solver->assert_formula(eq);

    size_t violated = 0;
    TermVec lits;
    lits.reserve(constraints.size());
    for (Term c : constraints) {
        Result r = solver->check_sat_assuming(TermVec{c});
        if(r.is_unsat())
            violated ++;
    }
    solver->pop();
    return violated;
}


TermVec get_hot_starting_point(
    const TermVec & constraints,
    const SmtSolver & solver,
    const UnorderedTermSet & free_symbols,
    unordered_map<Term,string> & model
){  
    TermVec eqs;
    TermVec only_one;
    if (!constraints.empty()) {
        only_one.reserve(constraints.size());
        // 第一个
        only_one.push_back(constraints[0]);

        // 其余取反
        for (size_t i = 1; i < constraints.size(); ++i) {
            Term c = constraints[i];
            // 断言布尔约束，否则无法取 Not
            assert(c->get_sort()->get_sort_kind() == BOOL &&
                   "constraint must be Boolean to apply NOT");
            only_one.push_back(solver->make_term(Not, c));
        }
    }
    Result r = solver->check_sat_assuming(only_one);
    if(r.is_sat()){
        for(auto sym : free_symbols){
            auto val = solver->get_value(sym);

            std::string bits = val->to_string();
            if (bits.rfind("#b", 0) == 0)
                bits = bits.substr(2);
            if (bits.size() < static_cast<size_t>(sym->get_sort()->get_width()))
                bits.insert(0, sym->get_sort()->get_width() - bits.size(), '0');
            model[sym] = std::move(bits);

            auto formula = solver->make_term(Equal, sym, val);
            eqs.push_back(formula);
        }
    }

    return eqs;
}

void reduce_unsat_core_to_fixedpoint(
    smt::UnorderedTermSet & core_inout,
    const smt::SmtSolver & reducer_,
    Result& r) 
{
    if (core_inout.empty()) {
        r = reducer_->check_sat();
        return;
    }

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



inline void generate_neighbour(
        std::unordered_map<Term, std::string>   & m,
        const UnorderedTermSet                  & free_syms,
        std::mt19937                            & rng,
        GmpRandStateGuard                       & rand_guard,
        double                                    T,
        double                                    T_split,
        double                                    T_freeze)
{
    /* ---------- 常用分布 ---------- */
    std::uniform_real_distribution<double> urd(0.0, 1.0);
    std::bernoulli_distribution bool_coin(0.5);          // 生成 BOOL
    std::bernoulli_distribution pick_sym_mid(0.25);      // 中温：25 % 选符号
    std::uniform_real_distribution<double> flip_rate(0.05, 0.20); // 中温位翻转比例

    /* ============================================================
     *             2. 中温区：中尺度扰动（多符号）
     * ============================================================ */
    if (T >= T_freeze) {
        for (const Term & s : free_syms) {
            if (!pick_sym_mid(rng)) continue;            // 75 % 留空
            Sort sort = s->get_sort();
            if (sort->get_sort_kind() == BOOL) {
                m[s] = (m[s] == "1" ? "0" : "1");        // BOOL 直接取反
            } else {
                int w = sort->get_width();
                std::string &bits = m[s];
                /* ——— 保证 bit‑vector 已初始化 ——— */
                if (bits.empty()) {
                    mpz_t mp; rand_guard.random_input(mp, w);
                    std::unique_ptr<char, void(*)(void*)> tmp(mpz_get_str(nullptr, 2, mp), free);
                    bits.assign(tmp.get());
                    if (bits.size() < static_cast<size_t>(w))
                        bits.insert(0, w - bits.size(), '0');
                    mpz_clear(mp);
                }
                /* —— 按 5‑20 % 比例翻转随机位 —— */
                size_t flip_cnt = std::max<size_t>(1, w * flip_rate(rng));
                for (size_t i = 0; i < flip_cnt; ++i) {
                    size_t pos = std::uniform_int_distribution<size_t>(0, w - 1)(rng);
                    bits[w - 1 - pos] = (bits[w - 1 - pos] == '0' ? '1' : '0');
                }
            }
        }
        return;
    }

    /* ============================================================
     *               3. 低温区：局部微扰（单符号）
     * ============================================================ */
    std::bernoulli_distribution pick_sym_low(0.05);      // 5 % 选符号
    for (const Term & s : free_syms) {
        if (!pick_sym_low(rng)) continue;
        Sort sort = s->get_sort();
        if (sort->get_sort_kind() == BOOL) {
            m[s] = (m[s] == "1" ? "0" : "1");
        } else {
            int w = sort->get_width();
            std::string &bits = m[s];
            if (bits.empty()) {
                mpz_t mp; rand_guard.random_input(mp, w);
                std::unique_ptr<char, void(*)(void*)> tmp(mpz_get_str(nullptr, 2, mp), free);
                bits.assign(tmp.get());
                if (bits.size() < static_cast<size_t>(w))
                    bits.insert(0, w - bits.size(), '0');
                mpz_clear(mp);
            }

            double r = urd(rng);
            if (r < 0.33) {
                /* ---- ① 翻转 1 bit ---- */
                size_t pos = std::uniform_int_distribution<size_t>(0, w - 1)(rng);
                bits[w - 1 - pos] = (bits[w - 1 - pos] == '0' ? '1' : '0');
            } else if (r < 0.66) {
                /* ---- ② 翻转一半 bits ---- */
                size_t half = w / 2;
                std::unordered_set<size_t> flipped;
                while (flipped.size() < half) {
                    size_t pos = std::uniform_int_distribution<size_t>(0, w - 1)(rng);
                    if (flipped.insert(pos).second)
                        bits[w - 1 - pos] = (bits[w - 1 - pos] == '0' ? '1' : '0');
                }
            } else {
                /* ---- ③ 全量重采样 ---- */
                mpz_t mp; rand_guard.random_input(mp, w);
                std::unique_ptr<char, void(*)(void*)> tmp(mpz_get_str(nullptr, 2, mp), free);
                std::string newbits(tmp.get());
                if (newbits.size() < static_cast<size_t>(w))
                    newbits.insert(0, w - newbits.size(), '0');
                bits.swap(newbits);
                mpz_clear(mp);
            }
        }
    }
}




struct SAParams {
    size_t  max_iters     = 50000;    // 总迭代次数
    double  T_init        = 60.0;     // 初始温度
    double  T_min         = 0.01;     // 终止温度
    double  alpha         = 0.995;    // 温度衰减因子
    size_t  eval_batch    = 64;       // 每次随机扰动的输入个数
    double T_split        = T_init * 0.5;     // 温度分裂点
    double  T_freeze      = T_init * 0.25;    // 低于此温度即冻结
    double max_violation_rate  = 0.1;  // 最大允许违例率
};


static inline std::string encode_model(const unordered_map<Term,std::string>& m) {
    // 推荐：指针地址 + 位串
    std::ostringstream oss;
    for (const auto &kv : m) {
        oss << kv.first.get() << ':' << kv.second << ';'; // get() 取 shared_ptr 内部裸指针
    }
    return oss.str();
}



/* ============================================================
 *  SA core
 * ============================================================ */
unordered_map<Term,string> simulated_annealing_search(
        const UnorderedTermSet & free_symbols,
        const TermVec & constraints,
        const SmtSolver & solver,
        std::vector<unordered_map<Term,std::string>> & elite_out, 
        size_t desired_elite = 1,
        const SAParams & p = SAParams()
) {
     /* ---------- ① 统一 RNG ---------- */
    std::mt19937 rng(static_cast<uint32_t>(std::chrono::steady_clock::now().time_since_epoch().count()));
    std::uniform_real_distribution<double> urd(0.0, 1.0);

    GmpRandStateGuard rand_guard;

    const size_t total_constraints = constraints.size();
    const size_t max_violations = static_cast<size_t>(std::ceil(total_constraints * p.max_violation_rate));

    unordered_map<Term,string> model;
    // TermVec assumptions = random_simulation(free_symbols, solver, rand_guard, model);
    TermVec assumptions = get_hot_starting_point(constraints, solver, free_symbols, model);

    size_t best_E = evaluate_energy(constraints, assumptions, solver);
    size_t curr_E = best_E;
    auto   best_model = model;
    vector<unordered_map<Term,string>> elite_pool;
    encode_model(best_model);
    unordered_set<std::string> elite_sig;
    elite_sig.insert(encode_model(best_model));

    double T = p.T_init;

    // ------- SA main loop ------
    for (size_t iter=0; iter < p.max_iters && T > p.T_min; ++iter, T *= p.alpha) {
        unordered_map<Term,string> new_model = model;

        //TODO generate neighbour
        generate_neighbour(new_model, free_symbols, rng, rand_guard, T, p.T_split, p.T_freeze);

        TermVec new_assum = rebuild_assumptions(new_model, solver);
        size_t new_E = evaluate_energy(constraints, new_assum, solver);

        double deltaE   = double(new_E) - double(curr_E);
        double prob     = std::exp(-deltaE / T);
        bool   improve  = (new_E < curr_E);
        bool accept;
        if (T <= p.T_freeze) {
            accept = improve;
        } else {
            accept = improve || (urd(rng) < prob);
        }

        if(!accept) continue;
        model.swap(new_model);
        assumptions.swap(new_assum);
        curr_E = new_E;
        std::string sig = encode_model(model);

        if(curr_E <= max_violations && elite_sig.find(sig) == elite_sig.end()) {
            // 如果当前能量小于最大违例，且模型未被收录，则将当前模型添加到精英池中
            std::string sig = encode_model(model);
            if (elite_sig.insert(sig).second)
                elite_pool.push_back(model);
            if (elite_pool.size() >= desired_elite) {
                std::cout << "[SA] collect " << elite_pool.size() << " elite models, early stop." << std::endl;
                break;
            }
            T = p.T_init;                       // 温度复位
            model.clear();                      // 丢弃旧模型
            assumptions = random_simulation(
                              free_symbols,
                              solver,
                              rand_guard,
                              model);           // 全随机采样
            curr_E = evaluate_energy(constraints,
                                     assumptions,
                                     solver);   // 更新能量
            continue;                           // 开启下一轮迭代
        }

        if (new_E < best_E) {
            best_E     = new_E;
            best_model = model;
        }
        
        if (elite_pool.size() >= desired_elite) {
            std::cout << "[SA] Collected " << elite_pool.size() << " stimuli, early stop.\n";
            break;
        }
        
        if( iter % 100 == 0){
            std::cout << "[SA] Iter: " << iter
                      << " , T: " << T
                      << " , E: " << curr_E
                      << " , B: " << best_E
                      << " , S: " << elite_pool.size()
                      << '\n';
        }        
        
    }

    std::cout << "[SA END] violations= " << best_E
              << ", elite= " << elite_pool.size() << '\n';

    elite_out = elite_pool;
    return best_model;
}



/* ---------- write file ---------- */
void write_stimulus_file(const unordered_map<Term,string>& mp,
                         const string& path)
{
    ofstream ofs(path);
    for (auto &[sym,bits]:mp)
        ofs<<"EQ "<<sym->to_string()<<' '<<bits<<'\n';
}

/* ---------- simple conjunction helper ---------- */
static Term and_vec(const TermVec & v, SmtSolver & s)
{
    if (v.empty()) return s->make_term(true);
    Term ret = v[0];
    for (size_t i=1;i<v.size();++i)
        ret = s->make_term(And, ret, v[i]);
    return ret;
}

/* ---------- append one stimulus block ---------- */
void append_stimulus_block(std::ofstream & ofs,
                           const unordered_map<Term,string> & mp,
                           size_t iter)
{
    ofs << "[SIMULATION ITERATION " << iter << "]\n";
    for (auto &[sym, bits] : mp)
        ofs << sym->to_string() << " = " << bits << '\n';
    ofs << '\n';
}

/* ============================================================
 *  main
 * ============================================================ */
int main(int argc,char*argv[])
{
    if (argc!=4){
        cerr<<"Usage: "<<argv[0]<<" <file.btor2> <bound> <out_stimulus>\n";
        return 1;
    }
    string btor2_file=argv[1];
    int    bound=stoi(argv[2]);
    string out_file=argv[3];

    /* ---------- solver & TS ---------- */
    SmtSolver solver=BitwuzlaSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental","true");
    solver->set_opt("produce-models","true");
    solver->set_opt("produce-unsat-assumptions","true");

    TransitionSystem sts(solver);
    BTOR2Encoder enc(btor2_file,sts);

    SymbolicSimulator sim(sts,solver);
    sim.init(); sim.set_input({}, {});

    if (sts.prop().empty()){
        cout<<"No property!\n"; return 0;
    }
    Term prop = and_vec(sts.prop(), solver);

    /* ---------- unroll ---------- */
    for(int i=1;i<=bound;++i) { 
        sim.sim_one_step(); 
        sim.set_input({},{}); 
    }

    TermVec constraints = sim.all_assumptions();
    TermVec atoms = flatten_and_constraints(constraints);
    std::cout << "[Init]C : " << constraints.size() << ", atoms: " << atoms.size() << std::endl;

    /* free symbols */
    UnorderedTermSet free_symbols;
    Term root = sim.interpret_state_expr_on_curr_frame(prop,false);
    smt::get_free_symbols(root, free_symbols);
    std::cout<<"[Init] Free symbols = "<< free_symbols.size() << std::endl;

    SAParams par; 
    std::vector<unordered_map<Term,string>> elite_pool;
    const size_t TARGET = 100;
    simulated_annealing_search(free_symbols, atoms, solver, elite_pool, TARGET, par);



    std::ofstream ofs(out_file);
    for (size_t i = 0; i < elite_pool.size(); ++i)
        append_stimulus_block(ofs, elite_pool[i], i + 1);
    ofs.close();
    std::cout << "Stimuli (total " << elite_pool.size() << ") written to " << out_file << '\n';

    return 0;
}