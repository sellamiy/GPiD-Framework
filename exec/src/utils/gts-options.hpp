#ifndef GPID_EXEC__UTILS__GTS_OPTIONS_HPP
#define GPID_EXEC__UTILS__GTS_OPTIONS_HPP

#include <vector>
#include <cxxopts.hpp>
#include <dot/dotcommand.hpp>
#include <witchw/witchw.hpp>
#include <gpid/gpid.hpp>

/* ===== Structures ===== */

#ifndef SINGLE_SOLVER_ONLY
#include <gpid/solver-snippets/gts-interfaces.hpp>
#endif

struct OptionStorage : public gpid::CoreOptions {
    std::string input;
    std::string input_lang;
#ifndef SINGLE_SOLVER_ONLY
    EngineSelection generator;
#endif

    witchw::wController control;
};

enum OptionStatus {
    OK, ENDED, FAILURE
};

static inline OptionStatus parseOptions(OptionStorage& opts, int argc, char** argv);
static inline OptionStatus handleOptions(OptionStorage& opts, cxxopts::Options& parser);
static inline OptionStatus detectConflicts(OptionStorage& opts, cxxopts::Options& parser);

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
            ("input-language", "Language of input file", cxxopts::value<std::string>())
	    ;

#ifndef SINGLE_SOLVER_ONLY
        parser.add_options("Generator")
            ("g,generator",
             "Generator to use in [" + gpid::list_configured_generators() + "]",
             cxxopts::value<std::string>())
            ;
#endif

        parser.add_options("Engine")
            ("s,store-implicates", "Allow generated implicate to be stored")
            ("dont-store-implicates", "Allow generated implicate to be stored")

            ("use-models", "Use solver models to prune hypotheses sets")
            ("dont-use-models", "Do not use solver models")

            ("allow-inconsistencies", "Let the engine generate inconsistent implicates")
            ("dont-allow-inconsistencies", "Force the engine generate consistent implicates only")

            ("implicate-size-limit", "Max number of abducibles in implicates", cxxopts::value<uint32_t>())

            ("time-limit", "Maximal generation time allowed (seconds)", cxxopts::value<uint64_t>())
            ("implicate-limit", "Maximal number of implicates to generate", cxxopts::value<uint64_t>())
            ;

	parser.add_options("Output")
	    ("p,print-implicates", "Print generated implicates")
	    ("dont-print-implicates", "Do not print generated implicates")
#ifdef DOT_FOUND
            ("dot-autocompile", "Autocompile dot graphs")
#endif
	    ;

        parser.add_options("Instrument")
            ("generate-selection-graph", "Generate a selection graph via instrumentation",
             cxxopts::value<std::string>())
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
#ifndef SINGLE_SOLVER_ONLY
        std::vector<std::string> help_cats = {"", "Generator", "Input", "Output", "Engine", "Instrument"};
#else
        std::vector<std::string> help_cats = {"", "Input", "Output", "Engine", "Instrument"};
#endif
	if (parser.count("help")) {
	    snlog::l_message(parser.help(help_cats));
	    return OptionStatus::ENDED;
	}
	if (parser.count("version")) {
	    snlog::l_message(gpid::generate_version_message());
	    return OptionStatus::ENDED;
	}

	if (parser.count("print-implicates"))
	    opts.engine.print_implicates = true;
	if (parser.count("dont-print-implicates"))
	    opts.engine.print_implicates = false;

        if (parser.count("store-implicates"))
	    opts.engine.store_implicates = true;
	if (parser.count("dont-store-implicates"))
	    opts.engine.store_implicates = false;

        if (parser.count("use-models"))
	    opts.engine.use_models = true;
	if (parser.count("dont-use-models"))
	    opts.engine.use_models = false;

        if (parser.count("allow-inconsistencies"))
	    opts.engine.allow_inconsistencies = true;
	if (parser.count("dont-allow-inconsistencies"))
	    opts.engine.allow_inconsistencies = false;

        if (parser.count("implicate-size-limit"))
            opts.engine.max_level = parser["implicate-size-limit"].as<uint32_t>() + 1;

        if (parser.count("time-limit"))
            opts.engine.time_limit = parser["time-limit"].as<uint64_t>();
        if (parser.count("implicate-limit"))
            opts.engine.implicate_limit = parser["implicate-limit"].as<uint64_t>();

	if (parser.count("input")) {
	    opts.input = parser["input"].as<std::string>();
	} else {
	    snlog::l_fatal("No input file provided");
	    snlog::l_info(parser.help({"Input"}));
	    return OptionStatus::FAILURE;
	}

        if (parser.count("input-language")) {
	    opts.input_lang = parser["input-language"].as<std::string>();
	} else {
            // TODO: Show meaningful info message here
            opts.input_lang = "default";
	}

#ifndef SINGLE_SOLVER_ONLY
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
#endif

        if (parser.count("load-abducibles")) {
            opts.abducibles.input_type = gpid::AbdInputType::ABDIT_FILE;
            opts.abducibles.input_file = parser["load-abducibles"].as<std::string>();
        }

        if (parser.count("autogen-abducibles")) {
            opts.abducibles.input_type = gpid::AbdInputType::ABDIT_GENERATOR;
            opts.abducibles.input_generator = parser["autogen-abducibles"].as<std::string>();
        }

        if (parser.count("generate-selection-graph")) {
            opts.instrument.selection_graph = true;
            opts.instrument.selection_graph_file = parser["generate-selection-graph"].as<std::string>();
        }

#ifdef DOT_FOUND
        if (parser.count("dot-autocompile")) {
            opts.instrument.autocompile_graphs = true;
        }
#endif

	return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

/* ===== Detectors ===== */

static inline OptionStatus detectConflicts(OptionStorage&, cxxopts::Options& parser) {
    try {

        /* Incompatible options */
        const std::vector<std::vector<std::string>> p_illeg
        {
            { "load-abducibles", "autogen-abducibles" },
            { "print-implicates", "dont-print-implicates"},
            { "store-implicates", "dont-store-implicates"},
            { "use-models", "dont-use-models"},
            { "allow-inconsistencies", "dont-allow-inconsistencies" }
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

        /* Inactive options */
#ifndef GPID_INSTRUMENTATION
        const std::vector<std::string> instr_opts
        { "generate-selection-graph" };
        for (uint32_t pc = 0; pc < instr_opts.size(); pc++) {
            if (parser.count(instr_opts[pc])) {
                snlog::l_fatal("Option uses instrumentation but instrumentation is not configured:");
                snlog::l_info("   @option: " + instr_opts[pc]);
                return OptionStatus::FAILURE;
            }
        }
#endif

        return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

#endif
