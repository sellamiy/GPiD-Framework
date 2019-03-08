#define ABDULOT_PARSER_CPP

#include <cxxopts.hpp>
#include <snlog/snlog.hpp>
#include <abdulot/core/errors.hpp>
#include <abdulot/reference/version.hpp>
#include <abdulot/utils/abducibles-core.hpp>

/* ========== Options ========== */

/* ===== Structures ===== */

/** Local options for the executable. */
struct ParserOptions {
    std::vector<std::string> inputs;
    bool abducible = false;
    bool countonly = false;
};

enum class OptionStatus {
    OK, ENDED, FAILURE
};

static inline OptionStatus parseOptions(ParserOptions& opts, int& argc, char**& argv);
static inline OptionStatus handleOptions
(ParserOptions& opts, cxxopts::Options& parser, cxxopts::ParseResult& results);

/* ===== Parser ===== */

static inline OptionStatus parseOptions(ParserOptions& opts, int& argc, char**& argv) {
    try {

	cxxopts::Options parser(argv[0], abdulot::project_full_name + "--parser");

	parser.add_options()
	    ("h,help", "Print this help message")
	    ("v,version", "Print framework version")

            ("i,input", "Input files", cxxopts::value<std::vector<std::string>>(opts.inputs))

            ("a,abducible-output", "Output data in abducible format")

            ("c,count-only", "Only give the number of abducibles")
	    ;

        parser.parse_positional({"input"});
        parser.positional_help("<input-file.abd> ...");

	cxxopts::ParseResult results = parser.parse(argc, argv);

	return handleOptions(opts, parser, results);

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error() << e.what() << snlog::l_end;
	return OptionStatus::FAILURE;
    }
}

/* ===== Handler ===== */

static inline OptionStatus handleOptions
(ParserOptions& opts, cxxopts::Options& parser, cxxopts::ParseResult& results) {
    try {

	if (results.count("help")) {
	    snlog::l_message() << parser.help({""}) << snlog::l_end;
	    return OptionStatus::ENDED;
	}
	if (results.count("version")) {
	    snlog::l_message() << abdulot::version_message << snlog::l_end;
	    return OptionStatus::ENDED;
	}
        if (results.count("abducible-output")) {
            opts.abducible = true;
        }
        if (results.count("count-only")) {
            opts.countonly = true;
        }

	return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error() << e.what() << snlog::l_end;
	return OptionStatus::FAILURE;
    }
}

using namespace std;
using namespace snlog;
using namespace abdulot;

/* ========== Main Helpers ========== */

static int handle_input(const std::string& input, const ParserOptions& opts) {
    AbducibleParser parser(input);
    t_fatal(!parser.isValid()) << "Parser in broken state; please stop!" << l_end;

    if (opts.abducible) {

        std::cout << "(size " << parser.getAbducibleCount() << ")" << std::endl
                  << "(rsize " << parser.getReferenceCount() << ")" << std::endl;

        if (!opts.countonly) {

            for (uint32_t i = 0; i < parser.getAbducibleCount(); i++) {
                std::cout << "(abduce " << parser.nextAbducible() << ")" << std::endl;
            }

            for (uint32_t i = 0; i < parser.getReferenceCount(); i++) {
                std::cout << "(reference " << parser.nextReference() << ")" << std::endl;
            }

        }

    } else {

        l_notif() << "number of abducibles" << " : " << parser.getAbducibleCount() << l_end;
        l_notif() << "number of references" << " : " << parser.getReferenceCount() << l_end;

        if (!opts.countonly) {

            for (uint32_t i = 0; i < parser.getAbducibleCount(); i++) {
                l_notifg() << "abducible" << " : " << parser.nextAbducible() << l_end;
            }

            for (uint32_t i = 0; i < parser.getReferenceCount(); i++) {
                l_notifg() << "reference" << " : " << parser.nextReference() << l_end;
            }

        }

    }

    if (parser.isValid()) {
        l_message() << "complete." << l_end;
        return EXIT_SUCCESS;
    } else {
        l_fatal() << "errors were raised." << l_end;
        return EXIT_FAILURE;
    }
}

/* ========== Main ========== */

int main(int argc, char** argv) {
    ParserOptions opts;
    OptionStatus status = parseOptions(opts, argc, argv);
    if (status == OptionStatus::FAILURE) {
	return EXIT_FAILURE;
    } else if (status == OptionStatus::ENDED) {
	return EXIT_SUCCESS;
    }

    l_message() << "start abducible parser..." << l_end;

    try {
        for (const std::string& input : opts.inputs) {
            int rv = handle_input(input, opts);
            if (rv != EXIT_SUCCESS) {
                return EXIT_FAILURE;
            }
        }
    } catch (abdulot::CoreError& e) {
        snlog::l_fatal() << e.what() << snlog::l_end;
        return EXIT_FAILURE;
    }
}
