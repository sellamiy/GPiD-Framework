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
    SMT_Z3,
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
static inline OptionStatus detectConflicts(OptionStorage& opts, cxxopts::Options& parser);

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
    if (v == "z3") {
#ifdef Z3_SOLVER_INTERFACE
        return EngineSelection::SMT_Z3;
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
            ("l,load-abducibles", "Abducible file", cxxopts::value<std::string>())
            ("a,autogen-abducibles", "Abducible auto generation type", cxxopts::value<std::string>())
	    ;

        parser.add_options("Generator")
            ("g,generator",
             "Generator to use in [" + gpid::list_configured_generators() + "]",
             cxxopts::value<std::string>())
            ;

        parser.add_options("Engine")
            ("s,store-implicates", "Allow generated implicate to be stored")
            ("dont-store-implicates", "Allow generated implicate to be stored")
            ;

	parser.add_options("Output")
	    ("p,print-implicates", "Print generated implicates")
	    ("no-print-implicates", "Do not print generated implicates")
	    ;

	parser.parse(argc, argv);

        OptionStatus str = detectConflicts(opts, parser);
        return str == OptionStatus::OK ? handleOptions(opts, parser) : str;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

/* ===== Handler ===== */

static inline OptionStatus handleOptions(OptionStorage& opts, cxxopts::Options& parser) {
    try {

	if (parser.count("help")) {
	    snlog::l_message(parser.help({"", "Generator", "Input", "Output", "Engine"}));
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

        if (parser.count("store-implicates")) {
	    opts.engine.store_implicates = true;
	}
	if (parser.count("dont-store-implicates")) {
	    opts.engine.store_implicates = false;
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

        if (parser.count("load-abducibles")) {
            opts.abducibles.input_type = gpid::AbdInputType::ABDIT_FILE;
            opts.abducibles.input_file = parser["load-abducibles"].as<std::string>();
        }

        if (parser.count("autogen-abducibles")) {
            opts.abducibles.input_type = gpid::AbdInputType::ABDIT_GENERATOR;
            opts.abducibles.input_generator = parser["autogen-abducibles"].as<std::string>();
        }

	return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

/* ===== Detectors ===== */

static inline OptionStatus detectConflicts(OptionStorage&, cxxopts::Options& parser) {
    try {

        const std::vector<std::vector<std::string>> p_illeg
        {
            { "load-abducibles", "autogen-abducibles" },
            { "store-implicates", "dont-store-implicates"}
        };

        for (uint32_t pc = 0; pc < p_illeg.size(); pc++) {
            bool active = true;
            for (uint32_t lc = 0; lc < p_illeg[pc].size(); lc++)
                if (!parser.count(p_illeg[pc][lc])) active = false;
            if (active) {
                snlog::l_fatal("Conflictual options detected:");
                for (uint32_t lc = 0; lc < p_illeg[pc].size(); lc++)
                    snlog::l_info("   @option: " + p_illeg[pc][lc]);
                return OptionStatus::FAILURE;
            }
        }

        return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

#endif
