#ifndef GPID_EXEC__UTILS__ILINVA_OPTIONS_HPP
#define GPID_EXEC__UTILS__ILINVA_OPTIONS_HPP

#include <cxxopts.hpp>
#include <snlog/snlog.hpp>
#include <lcdot/dotcommand.hpp>
#include <stdutils/stats-controller.hpp>
#include <stdutils/strings.hpp>
#include <abdulot/core/algorithm.hpp>
#include <abdulot/reference/version.hpp>
#include <abdulot/ilinva/options.hpp>
#include <abdulot/instrument/options.hpp>

/* ===== Structures ===== */

#ifndef SINGLE_SOLVER_ONLY
#include "sai/identifiers.hpp"
#endif

/** Local option aggregator for executables. */
struct OptionStorage : public abdulot::AlgorithmOptions
{
#ifndef SINGLE_SOLVER_ONLY
    interface_id interface;
#endif

    abdulot::ilinva::IlinvaOptions ilinva;
    abdulot::instrument::InstrumentOptions instrument;
    stdutils::StatisticController control;
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
            ("a,override-abducibles", "Abducible file", cxxopts::value<std::string>())
	    ;

#ifndef SINGLE_SOLVER_ONLY
        parser.add_options("Generator")
            ("g,generator",
             "Generator to use in [" + interface_id_list + "]",
             cxxopts::value<std::string>())
            ;
#endif

        parser.add_options("Engine")
            ("t,time-limit", "Maximal generation time allowed (seconds)", cxxopts::value<uint64_t>())
            ("d,depth-limit", "Maximal strengthening depth allowed", cxxopts::value<uint32_t>())
            ("c,conjunctive-only", "Only seek conjunctive loop invariants", cxxopts::value<bool>())
            ("r,randomize-literals", "Randomize (once) the abducible literals", cxxopts::value<bool>())
            ("s,max-strengthening-size", "Maximal depth of the abduction", cxxopts::value<uint32_t>())
            ("smt-time-limit", "Timeout for abduction smt tests (seconds)", cxxopts::value<uint64_t>())
            ("small-smt-time-limit", "Same as smt-time-limit, with float handle", cxxopts::value<double>())
            ("u,no-insurance-checks", "Remove abducible literals validity checks", cxxopts::value<bool>())
            ("H,handler-option", "Forward option to code handler (format optname:optvalue)",
             cxxopts::value<std::vector<std::string>>())
            ;

	parser.add_options("Output")
            ("time-unit", "Unit for printing time data (truncated)", cxxopts::value<std::string>())
            ("o,output", "Output file for results", cxxopts::value<std::string>())
	    ;

        // parser.add_options("Instrument")

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
        std::vector<std::string> help_cats = {"", "Generator", "Input", "Output", "Engine"};
#else
        std::vector<std::string> help_cats = {"", "Input", "Output", "Engine"};
#endif
	if (results.count("help")) {
	    snlog::l_message() << parser.help(help_cats) << snlog::l_end;
	    return OptionStatus::ENDED;
	}
	if (results.count("version")) {
	    snlog::l_message() << abdulot::version_message << snlog::l_end;
	    return OptionStatus::ENDED;
	}

        if (results.count("time-limit"))
            opts.core.time_limit = results["time-limit"].as<uint64_t>();

        if (results.count("depth-limit"))
            opts.ilinva.max_depth = results["depth-limit"].as<uint32_t>();

        if (results.count("conjunctive-only"))
            opts.ilinva.disjunct = false;

        if (results.count("randomize-literals"))
            opts.ilinva.shuffle_literals = true;

        if (results.count("no-insurance-checks"))
            opts.ilinva.insurance_checks = false;

        if (results.count("max-strengthening-size"))
            opts.ilinva.max_strengthening_size = results["max-strengthening-size"].as<uint32_t>();

        if (results.count("smt-time-limit"))
            opts.ilinva.smt_time_limit = results["smt-time-limit"].as<uint64_t>();

        if (results.count("small-smt-time-limit"))
            opts.ilinva.small_smt_time_limit = results["small-smt-time-limit"].as<double>();

        if (results.count("output"))
	    opts.ilinva.output = results["output"].as<std::string>();

        if (results.count("override-abducibles"))
            opts.ilinva.abd_override = results["override-abducibles"].as<std::string>();

	if (results.count("input")) {
	    opts.ilinva.input_file = results["input"].as<std::string>();
	} else {
	    snlog::l_fatal() << "No input file provided" << snlog::l_end
                             << snlog::l_info << parser.help({"Input"})
                             << snlog::l_end;
	    return OptionStatus::FAILURE;
	}

        if (results.count("handler-option")) {
            for (const std::string& optdata : results["handler-option"].as<std::vector<std::string>>()) {
                if (stdutils::count(optdata, ":") != 1) {
                    snlog::l_error() << "Illegal code handler option format: " << optdata << snlog::l_end;
                } else {
                    const auto soptdata = stdutils::split(optdata, ":");
                    opts.ilinva.handler_options[soptdata[0]] = soptdata[1];
                }
            }
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

        if (results.count("time-unit")) {
            std::string ru_tunit = results["time-unit"].as<std::string>();
            if (ru_tunit != opts.control.time.selectDurationUnit(ru_tunit)) {
                snlog::l_fatal() << "Unknown time unit: " << ru_tunit << snlog::l_end;
                return OptionStatus::FAILURE;
            }
        }

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
            { "small-smt-time-limit", "smt-time-limit" }
            // { "opt1", "opt2" }
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
        { };
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
