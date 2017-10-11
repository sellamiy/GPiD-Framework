#ifndef _INCL_EX_OPTIONS_PARSER_
#define _INCL_EX_OPTIONS_PARSER_

#include <vector>
#include <cxxopts/cxxopts.hpp>
#include <gpid/gpid.hpp>

/* ===== Structures ===== */

enum EngineSelection {
    TRUE_SOLVER,
    MINISAT,
    SMT_CVC4,
    UNCONFIGURED_INTERFACE,
    UNKNOWN_INTERFACE
};

struct OptionStorage : public gpid::CoreOptions {
	std::string input;
        EngineSelection generator;
};

enum OptionStatus {
    OK, ENDED, FAILURE
};

static inline EngineSelection toEngineSelection(std::string v);
static inline OptionStatus parseOptions(OptionStorage& opts, int argc, char** argv);
static inline OptionStatus handleOptions(OptionStorage& opts, cxxopts::Options& parser);

/* ===== Converters ===== */

static inline EngineSelection toEngineSelection(std::string v) {
    if (v == "true-solver") {
#ifdef TRUE_SOLVER_INTERFACE
        return EngineSelection::TRUE_SOLVER;
#else
        return EngineSelection::UNCONFIGURED_INTERFACE;
#endif
    }
    if (v == "minisat") {
#ifdef MINISAT_SOLVER_INTERFACE
        return EngineSelection::MINISAT;
#else
        return EngineSelection::UNCONFIGURED_INTERFACE;
#endif
    }
    if (v == "cvc4") {
#ifdef CVC4_SOLVER_INTERFACE
        return EngineSelection::SMT_CVC4;
#else
        return EngineSelection::UNCONFIGURED_INTERFACE;
#endif
    }
    return EngineSelection::UNKNOWN_INTERFACE;
}

/* ===== Parser ===== */

static inline OptionStatus parseOptions(OptionStorage& opts, int argc, char** argv) {
    try {

	cxxopts::Options parser(argv[0], gpid::project_full_name);

	parser.add_options()
	    ("h,help", "Print this help message")
	    ("v,version", "Print framework version")
	    ;

	parser.add_options("Input")
	    ("i,input", "Input file", cxxopts::value<std::string>())
	    ;

        parser.add_options("Generator")
            ("g,generator",
             "Generator to use in [" + gpid::list_configured_generators() + "]",
             cxxopts::value<std::string>())
            ;

	parser.add_options("Output")
	    ("p,print-implicates", "Print generated implicates")
	    ("no-print-implicates", "Do not print generated implicates")
	    ;

	parser.parse(argc, argv);

	return handleOptions(opts, parser);

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

/* ===== Handler ===== */

static inline OptionStatus handleOptions(OptionStorage& opts, cxxopts::Options& parser) {
    try {

	if (parser.count("help")) {
	    snlog::l_message(parser.help({"", "Input", "Output"}));
	    return OptionStatus::ENDED;
	}
	if (parser.count("version")) {
	    snlog::l_message(gpid::generate_version_message());
	    return OptionStatus::ENDED;
	}

	if (parser.count("print-implicates")) {
	    opts.engine.print_implicates = true;
	}
	if (parser.count("no-print-implicates")) {
	    opts.engine.print_implicates = false;
	}

	if (parser.count("input")) {
	    opts.input = parser["input"].as<std::string>();
	} else {
	    snlog::l_fatal("No input file provided");
	    snlog::l_info(parser.help({"Input"}));
	    return OptionStatus::FAILURE;
	}

        if (parser.count("generator")) {
            opts.generator = toEngineSelection(parser["generator"].as<std::string>());
            if (opts.generator == EngineSelection::UNKNOWN_INTERFACE) {
                snlog::l_fatal("Unknown generator:" + parser["generator"].as<std::string>());
                snlog::l_info(parser.help({"Generator"}));
                return OptionStatus::FAILURE;
            } else if (opts.generator == EngineSelection::UNCONFIGURED_INTERFACE) {
                snlog::l_fatal(parser["generator"].as<std::string>() + " interface not configured");
                snlog::l_info(parser.help({"Generator"}));
                return OptionStatus::FAILURE;
            }
        } else {
            snlog::l_fatal("No generator selected");
            snlog::l_info(parser.help({"Generator"}));
            return OptionStatus::FAILURE;
        }

	return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

#endif
