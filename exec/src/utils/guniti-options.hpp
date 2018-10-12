#ifndef GPID_EXEC__UTILS__GUNITI_OPTIONS_HPP
#define GPID_EXEC__UTILS__GUNITI_OPTIONS_HPP

#include <cxxopts.hpp>
#include <lcdot/dotcommand.hpp>
#include <witchw/witchw.hpp>
#include <gpid/gpid.hpp>

/* ===== Structures ===== */

#ifndef SINGLE_SOLVER_ONLY
#include "sai/identifiers.hpp"
#endif

/** Local option aggregator for implicate generation executables. */
struct OptionStorage : public gpid::GPiDOptions
{
    std::string input;
    std::string input_lang;
#ifndef SINGLE_SOLVER_ONLY
    interface_id interface;
#endif

    gpid::GunitiOptions guniti;
    gpid::instrument::InstrumentOptions instrument;
    witchw::wController control;
    bool naive = false;
};

enum class OptionStatus {
    OK, ENDED, FAILURE
};

static inline OptionStatus parseOptions(OptionStorage& opts, int& argc, char**& argv);
static inline OptionStatus handleOptions
(OptionStorage& opts, cxxopts::Options& parser, cxxopts::ParseResult& results);
static inline OptionStatus detectConflicts
(OptionStorage& opts, cxxopts::Options& parser, cxxopts::ParseResult& results);

/* ===== Parser ===== */

static inline OptionStatus parseOptions(OptionStorage& opts, int& argc, char**& argv) {
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
             "Generator to use in [" + interface_id_list + "]",
             cxxopts::value<std::string>())
            ;
#endif

        parser.add_options("Engine")
            ("s,store-implicates", "Allow generated implicate to be stored")
            ("dont-store-implicates", "Allow generated implicate to be stored")

            ("use-models", "Use solver models to prune hypotheses sets")
            ("dont-use-models", "Do not use solver models")

            ("time-limit", "Maximal generation time allowed (seconds)", cxxopts::value<uint64_t>())
            ("implicate-limit", "Maximal number of implicates to generate", cxxopts::value<uint64_t>())
            ;

	parser.add_options("Output")
	    ("p,print-implicates", "Print generated implicates")
	    ("dont-print-implicates", "Do not print generated implicates")
            ("print-storage", "Print only stored implicates after computation")
	    ("dont-print-storage", "Do not print stored implicates")
            ("export-storage", "Export stored implicates in graph form after computation")
            ("time-unit", "Unit for printing time data (truncated)", cxxopts::value<std::string>())
#ifdef DOT_FOUND
            ("dot-autocompile", "Autocompile dot graphs")
#endif
	    ;

        parser.add_options("Instrument")
            ("generate-selection-graph", "Generate a selection graph via instrumentation",
             cxxopts::value<std::string>())
            ("generate-webtrace", "Generate a webtrace page via instrumentation",
             cxxopts::value<std::string>())
            ("infoline", "Infoline program data via instrumentation",
             cxxopts::value<bool>())
            ;

	cxxopts::ParseResult results = parser.parse(argc, argv);

        OptionStatus str = detectConflicts(opts, parser, results);
        return str == OptionStatus::OK ? handleOptions(opts, parser, results) : str;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

/* ===== Handler ===== */

static inline OptionStatus handleOptions
(OptionStorage& opts, cxxopts::Options& parser, cxxopts::ParseResult& results) {
    try {
#ifndef SINGLE_SOLVER_ONLY
        std::vector<std::string> help_cats = {"", "Generator", "Input", "Output", "Engine", "Instrument"};
#else
        std::vector<std::string> help_cats = {"", "Input", "Output", "Engine", "Instrument"};
#endif
	if (results.count("help")) {
	    snlog::l_message(parser.help(help_cats));
	    return OptionStatus::ENDED;
	}
	if (results.count("version")) {
	    snlog::l_message(gpid::version_message);
	    return OptionStatus::ENDED;
	}

	if (results.count("print-implicates"))
	    opts.guniti.print_implicates = true;
	if (results.count("dont-print-implicates"))
	    opts.guniti.print_implicates = false;

        if (results.count("store-implicates"))
	    opts.guniti.store_implicates = true;
	if (results.count("dont-store-implicates"))
	    opts.guniti.store_implicates = false;

        if (results.count("print-storage"))
	    opts.guniti.print_storage = true;
	if (results.count("dont-print-storage"))
	    opts.guniti.print_storage = false;

        if (results.count("export-storage"))
	    opts.guniti.export_storage = true;

        if (results.count("use-models"))
	    opts.guniti.use_models = true;
	if (results.count("dont-use-models"))
	    opts.guniti.use_models = false;

        if (results.count("time-limit"))
            opts.core.time_limit = results["time-limit"].as<uint64_t>();
        if (results.count("implicate-limit"))
            opts.guniti.implicate_limit = results["implicate-limit"].as<uint64_t>();

	if (results.count("input")) {
	    opts.input = results["input"].as<std::string>();
	} else {
	    snlog::l_fatal("No input file provided");
	    snlog::l_info(parser.help({"Input"}));
	    return OptionStatus::FAILURE;
	}

        if (results.count("input-language")) {
	    opts.input_lang = results["input-language"].as<std::string>();
	} else {
            // TODO: Show meaningful info message here
            opts.input_lang = "default";
	}

#ifndef SINGLE_SOLVER_ONLY
        if (results.count("generator")) {
            opts.interface = toInterfaceId(results["generator"].as<std::string>());
            if (opts.interface == interface_id::UNKNOWN_INTERFACE) {
                snlog::l_fatal("Unknown generator:" + results["generator"].as<std::string>());
                snlog::l_info(parser.help({"Generator"}));
                return OptionStatus::FAILURE;
            } else if (opts.interface == interface_id::UNCONFIGURED_INTERFACE) {
                snlog::l_fatal(results["generator"].as<std::string>() + " interface not configured");
                snlog::l_info(parser.help({"Generator"}));
                return OptionStatus::FAILURE;
            }
        } else {
            snlog::l_fatal("No generator selected");
            snlog::l_info(parser.help({"Generator"}));
            return OptionStatus::FAILURE;
        }
#endif

        if (results.count("load-abducibles")) {
            opts.guniti.input_type = gpid::AbducibleInputType::FILE;
            opts.guniti.input_file = results["load-abducibles"].as<std::string>();
        }

        if (results.count("autogen-abducibles")) {
            opts.guniti.input_type = gpid::AbducibleInputType::GENERATOR;
            opts.guniti.input_generator = results["autogen-abducibles"].as<std::string>();
        }

        if (results.count("time-unit")) {
            std::string ru_tunit = results["time-unit"].as<std::string>();
            if (ru_tunit != opts.control.time.selectDurationUnit(ru_tunit)) {
                snlog::l_fatal("Unknown time unit: " + ru_tunit);
                return OptionStatus::FAILURE;
            }
        }

        if (results.count("generate-selection-graph")) {
            opts.instrument.selection_graph = true;
            opts.instrument.selection_graph_file = results["generate-selection-graph"].as<std::string>();
        }
        if (results.count("generate-webtrace")) {
            opts.instrument.webtrace = true;
            opts.instrument.webtrace_file = results["generate-webtrace"].as<std::string>();
        }
        if (results.count("infoline")) {
            opts.instrument.infoliner = true;
        }

#ifdef DOT_FOUND
        if (results.count("dot-autocompile")) {
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

static inline OptionStatus detectConflicts
(OptionStorage&, cxxopts::Options&, cxxopts::ParseResult& results) {
    try {

        /* Incompatible options */
        const std::vector<std::vector<std::string>> p_illeg
        {
            { "load-abducibles", "autogen-abducibles" },
            { "print-implicates", "dont-print-implicates"},
            { "store-implicates", "dont-store-implicates"},
            { "print-storage", "dont-print-storage"},
            { "print-storage", "dont-store-implicates"},
            { "export-storage", "dont-store-implicates"},
            { "use-models", "dont-use-models"}
        };

        for (uint32_t pc = 0; pc < p_illeg.size(); pc++) {
            bool active = true;
            for (uint32_t lc = 0; lc < p_illeg[pc].size(); lc++)
                if (!results.count(p_illeg[pc][lc])) active = false;
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
        { "generate-selection-graph", "generate-webtrace", "infoline" };
        for (uint32_t pc = 0; pc < instr_opts.size(); pc++) {
            if (results.count(instr_opts[pc])) {
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
