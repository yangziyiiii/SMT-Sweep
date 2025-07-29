#include <iomanip>
#include <chrono>
#include <gmp.h>
#include <gmpxx.h>
#include <iostream>
#include <algorithm>
#include <random>
#include <atomic>
#include <getopt.h>


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