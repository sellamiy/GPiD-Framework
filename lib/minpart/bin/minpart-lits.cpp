#define MINPART_LITS_MMFP_EXECUTABLE_CPP

#include <ctime>

#include <cxxopts.hpp>
#include "shared.hpp"
#include <minpart-contexts/literals.hpp>
#include <minpart/generic-partitions.hpp>

using namespace std;
using namespace snlog;
using namespace minpart;

// c-bsize c-depth p-bsize p-depth size maxd mind

struct ExecOpts {
    literals::LiteralProblemOptions local;
    size_t size = 100;
    bool deterministic = false;
};

enum class OParseResult { Complete, ToForward, Failed };

static inline OParseResult parse_opts(ExecOpts& opts, int& argc, char**& argv) {
    try {
        cxxopts::Options parser(argv[0], LIBMINPART_NAME);

        parser.add_options()
            ("h,help", "Print this help message")
            ("v,version", "Print framework version")

            ("b,c-blocksize", "Block size for initials",
             cxxopts::value<size_t>(opts.local.c_blocksize))
            ("d,c-depth", "Block depth for initials",
             cxxopts::value<size_t>(opts.local.c_depth))
            ("B,p-blocksize", "Block size for partitions",
             cxxopts::value<size_t>(opts.local.p_blocksize))
            ("D,p-depth", "Block depth for partitions",
             cxxopts::value<size_t>(opts.local.p_depth))
            ("s,size", "Size of the hypotheses",
             cxxopts::value<size_t>(opts.size))
            ("m", "minimal generation depth",
             cxxopts::value<size_t>(opts.local.min_depth))
            ("M", "maximal generation depth",
             cxxopts::value<size_t>(opts.local.max_depth))
            ("n,deterministic", "Do not randomize inputs",
             cxxopts::value<bool>(opts.deterministic))
            ("r,random-partitions", "Randomize partitions",
             cxxopts::value<bool>(opts.local.random))
            ;

        cxxopts::ParseResult results = parser.parse(argc, argv);

        vector<string> hcats = {""};

        if (results.count("help")) {
            snlog::l_message() << parser.help(hcats) << snlog::l_end;
            return OParseResult::Complete;
        }
        if (results.count("version")) {
            snlog::l_message() << LIBMINPART_NAME << " vers. " << LIBMINPART_VERSION << snlog::l_end;
            return OParseResult::Complete;
        }

        return OParseResult::ToForward;
    } catch (const cxxopts::OptionException& e) {
	l_error() << e.what() << l_end;
	return OParseResult::Failed;
    }
}

static int handle_fwd(ExecOpts& opts) {
    if (!opts.deterministic) {
        srand (time(NULL));
    }

    l_notif() << "------------------------------" << l_end;
    l_notif() << "Generating initial problem..." << l_end;
    opts.local.problem = random_vector(opts.size, opts.local.max_depth, opts.local.min_depth);
    l_notifg() << "Generated!" << l_end;
    l_notif() << "------------------------------" << l_end;
    l_notif() << "Target printed below" << l_end;
    for (size_t i = 0; i < opts.local.problem.size() ; ++i)
        std::cout << i << '.' << opts.local.problem[i] << ' ';
    std::cout << std::endl;
    l_notif() << "------------------------------" << l_end;

    shared_execute_main<literals::LiteralProblemContext, GenericPartitionGenerator>(opts.local);

    return EXIT_SUCCESS;
}

int main(int argc, char** argv) {

    try {
        // Handle Options
        ExecOpts opts;
        OParseResult opr = parse_opts(opts, argc, argv);
        if (opr == OParseResult::Complete) return EXIT_SUCCESS;
        if (opr == OParseResult::Failed) return EXIT_FAILURE;
        return handle_fwd(opts);
    } catch (std::exception& e) {
        l_internal() << "Unexpected throwable recovered" << l_end
                     << l_fatal << e.what() << l_end;
    }

    return EXIT_FAILURE;
}
