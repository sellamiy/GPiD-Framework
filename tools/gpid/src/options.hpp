#ifndef GPID_EXEC__UTILS__IMPGEN_OPTIONS_HPP
#define GPID_EXEC__UTILS__IMPGEN_OPTIONS_HPP

#include <cxxopts.hpp>
#include <lcdot/dotcommand.hpp>
#include <stdutils/stats-controller.hpp>
#include <abdulot/core/algorithm.hpp>
#include <abdulot/reference/version.hpp>
#include <abdulot/gpid/options.hpp>
#include <abdulot/instrument/options.hpp>

/* ===== Structures ===== */

#ifndef SINGLE_SOLVER_ONLY
#include "sai/identifiers.hpp"
#endif

/** Local option aggregator for implicate generation executables. */
struct OptionStorage : public abdulot::AlgorithmOptions
{
    std::string input;
    std::string input_lang;
#ifndef SINGLE_SOLVER_ONLY
    interface_id interface;
#endif

    abdulot::gpid::GPiDOptions impgen;
    abdulot::instrument::InstrumentOptions instrument;
    stdutils::StatisticController control;
    bool naive = false;
    bool guniti_delegation = true;
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

	cxxopts::Options parser(argv[0], abdulot::project_full_name);

	parser.add_options()
	    ("h,help", "Print this help message")
	    ("v,version", "Print framework version")
	    ;

	parser.add_options("Input")
	    ("i,input", "Input file", cxxopts::value<std::string>())
            ("l,load-abducibles", "Abducible file", cxxopts::value<std::string>())
            ("autogen-abducibles", "Abducible auto generation type", cxxopts::value<std::string>())
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
            ("n,naive", "Generate implicates using the naive engine (trying all)")

            ("store-implicates", "Allow generated implicate to be stored")
            ("dont-store-implicates", "Allow generated implicate to be stored")

            ("use-models", "Use solver models to prune hypotheses sets")
            ("dont-use-models", "Do not use solver models")

            ("allow-inconsistencies", "Let the engine generate inconsistent implicates")
            ("dont-allow-inconsistencies", "Force the engine generate consistent implicates only")

            ("allow-guniti-delegation", "Let the engine generate inconsistent implicates")
            ("prevent-guniti-delegation", "Force the engine generate consistent implicates only")

            ("detect-consequences", "Let the engine detect and skip consequences of previous assignments")
            ("dont-detect-consequences", "Never detect consequences of selected abducibles")

            ("unknown-as-error", "Treat unknown solver results as errors")
            ("unknown-as-sat", "Treat unknown solver results as satisfiable results")
            ("unknown-as-unsat", "Treat unknown solver results as unsatisfiable results")

            ("d,implicate-size-limit", "Max number of abducibles in implicates", cxxopts::value<uint32_t>())

            ("t,time-limit", "Maximal generation time allowed (seconds)", cxxopts::value<uint64_t>())
            ("c,implicate-limit", "Maximal number of implicates to generate", cxxopts::value<uint64_t>())

            ("smt-time-limit", "Timeout for single smt tests (seconds)", cxxopts::value<uint64_t>())
            ;

	parser.add_options("Output")
	    ("p,print-implicates", "Print generated implicates")
	    ("dont-print-implicates", "Do not print generated implicates")
            ("P,print-storage", "Print only stored implicates after computation")
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
	snlog::l_error() << e.what() << snlog::l_end;
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
	    snlog::l_message() << parser.help(help_cats) << snlog::l_end;
	    return OptionStatus::ENDED;
	}
	if (results.count("version")) {
	    snlog::l_message() << abdulot::version_message << snlog::l_end;
	    return OptionStatus::ENDED;
	}

	if (results.count("print-implicates"))
	    opts.impgen.print_implicates = true;
	if (results.count("dont-print-implicates"))
	    opts.impgen.print_implicates = false;

        if (results.count("store-implicates"))
	    opts.impgen.store_implicates = true;
	if (results.count("dont-store-implicates"))
	    opts.impgen.store_implicates = false;

        if (results.count("print-storage"))
	    opts.impgen.print_storage = true;
	if (results.count("dont-print-storage"))
	    opts.impgen.print_storage = false;

        if (results.count("naive")) {
	    opts.naive = true;
            opts.impgen.use_models = false;
            opts.impgen.store_implicates = false;
            opts.impgen.detect_consequences = false;
            opts.impgen.print_storage = false;
            opts.impgen.export_storage = false;
        }

        if (results.count("export-storage"))
	    opts.impgen.export_storage = true;

        if (results.count("use-models"))
	    opts.impgen.use_models = true;
	if (results.count("dont-use-models"))
	    opts.impgen.use_models = false;

        if (results.count("allow-inconsistencies"))
	    opts.impgen.allow_inconsistencies = true;
	if (results.count("dont-allow-inconsistencies"))
	    opts.impgen.allow_inconsistencies = false;

        if (results.count("detect-consequences"))
            opts.impgen.detect_consequences = true;
        if (results.count("dont-detect-consequences"))
            opts.impgen.detect_consequences = false;

        if (results.count("allow-guniti-delegation"))
            opts.guniti_delegation = true;
        if (results.count("prevent-guniti-delegation"))
            opts.guniti_delegation = false;

        if (results.count("unknown-as-error"))
            opts.impgen.unknown_handle = abdulot::SolverTestStatus::UNKNOWN;
        if (results.count("unknown-as-sat"))
            opts.impgen.unknown_handle = abdulot::SolverTestStatus::SAT;
        if (results.count("unknown-as-unsat"))
            opts.impgen.unknown_handle = abdulot::SolverTestStatus::UNSAT;

        if (results.count("implicate-size-limit"))
            opts.impgen.max_level = results["implicate-size-limit"].as<uint32_t>() + 1;

        if (results.count("time-limit"))
            opts.core.time_limit = results["time-limit"].as<uint64_t>();
        if (results.count("implicate-limit"))
            opts.impgen.implicate_limit = results["implicate-limit"].as<uint64_t>();

        if (results.count("smt-time-limit"))
            opts.impgen.smt_time_limit = results["smt-time-limit"].as<uint64_t>();

	if (results.count("input")) {
	    opts.input = results["input"].as<std::string>();
	} else {
	    snlog::l_fatal() << "No input file provided" << snlog::l_end
                             << snlog::l_info << parser.help({"Input"})
                             << snlog::l_end;
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
                snlog::l_fatal()
                    << "Unknown generator:" << results["generator"].as<std::string>()
                    << snlog::l_end
                    << snlog::l_info << parser.help({"Generator"}) << snlog::l_end;
                return OptionStatus::FAILURE;
            } else if (opts.interface == interface_id::UNCONFIGURED_INTERFACE) {
                snlog::l_fatal()
                    << results["generator"].as<std::string>() << " interface not configured"
                    << snlog::l_end << snlog::l_info << parser.help({"Generator"})
                    << snlog::l_end;
                return OptionStatus::FAILURE;
            }
        } else {
            snlog::l_fatal() << "No generator selected" << snlog::l_end
                             << snlog::l_info << parser.help({"Generator"})
                             << snlog::l_end;
            return OptionStatus::FAILURE;
        }
#endif

        if (results.count("load-abducibles")) {
            opts.impgen.input_type = abdulot::gpid::AbducibleInputType::FILE;
            opts.impgen.input_file = results["load-abducibles"].as<std::string>();
        }

        if (results.count("autogen-abducibles")) {
            opts.impgen.input_type = abdulot::gpid::AbducibleInputType::GENERATOR;
            opts.impgen.input_generator = results["autogen-abducibles"].as<std::string>();
        }

        if (results.count("time-unit")) {
            std::string ru_tunit = results["time-unit"].as<std::string>();
            if (ru_tunit != opts.control.time.selectDurationUnit(ru_tunit)) {
                snlog::l_fatal() << "Unknown time unit: " << ru_tunit << snlog::l_end;
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
	snlog::l_error() << e.what() << snlog::l_end;
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
            { "use-models", "dont-use-models"},
            { "allow-inconsistencies", "dont-allow-inconsistencies" },
            { "detect-consequences", "dont-detect-consequences" },
            { "allow-guniti-delegation", "prevent-guniti-delegation" },
            { "naive", "store-implicates" },
            { "naive", "use-models" },
            { "naive", "detect-consequences" },
            { "naive", "print-storage" },
            { "naive", "export-storage" },
            { "unknown-as-error", "unknown-as-sat" },
            { "unknown-as-error", "unknown-as-unsat" },
            { "unknown-as-sat", "unknown-as-unsat" }
        };

        for (uint32_t pc = 0; pc < p_illeg.size(); pc++) {
            bool active = true;
            for (uint32_t lc = 0; lc < p_illeg[pc].size(); lc++)
                if (!results.count(p_illeg[pc][lc])) active = false;
            if (active) {
                snlog::l_fatal() << "Conflictual options detected:" << snlog::l_end;
                for (uint32_t lc = 0; lc < p_illeg[pc].size(); lc++)
                    snlog::l_info() << "   @option: " << p_illeg[pc][lc] << snlog::l_end;
                return OptionStatus::FAILURE;
            }
        }

        /* Inactive options */
#ifndef INSTRUMENTATION
        const std::vector<std::string> instr_opts
        { "generate-selection-graph", "generate-webtrace", "infoline" };
        for (uint32_t pc = 0; pc < instr_opts.size(); pc++) {
            if (results.count(instr_opts[pc])) {
                snlog::l_fatal() << "Option uses instrumentation but instrumentation is not configured:"
                                 << snlog::l_end << snlog::l_info
                                 << "   @option: " << instr_opts[pc] << snlog::l_end;
                return OptionStatus::FAILURE;
            }
        }
#endif

        return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error() << e.what() << snlog::l_end;
	return OptionStatus::FAILURE;
    }
}

#endif
