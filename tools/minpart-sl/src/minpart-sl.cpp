#define MINPART_SL_MMFP_EXECUTABLE_CPP

#include <ctime>

#include <cxxopts.hpp>
#include <bin/shared.hpp>
#include <context.hpp>
#include <minpart/generic-partitions.hpp>

using namespace std;
using namespace snlog;
using namespace minpart;

// c-bsize c-depth p-bsize p-depth size maxd mind

struct ExecOpts {
    slcvc::SLProblemOptions local;
    bool deterministic;

    ExecOpts(CVC4::ExprManager& em) : local(em), deterministic(false) {}
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
            ("n,deterministic", "Do not randomize inputs",
             cxxopts::value<bool>(opts.deterministic))
            ("r,random-partitions", "Randomize partitions",
             cxxopts::value<bool>(opts.local.random))
            ("i,input-file", "Input SL formula file",
             cxxopts::value<std::string>(opts.local.input_file))
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
    l_notif() << "Loading Solver..." << l_end;
    l_notif() << "------------------------------" << l_end;
    l_notif() << "------------------------------" << l_end;

    shared_execute_main<slcvc::SLProblemContext, GenericPartitionGenerator>(opts.local);

    return EXIT_SUCCESS;
}

int main(int argc, char** argv) {

    try {
        // Handle Options
        CVC4::ExprManager em;
        ExecOpts opts(em);
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
