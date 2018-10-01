#ifndef GPID_EXEC__UTILS__MASMALIG_OPTIONS_HPP
#define GPID_EXEC__UTILS__MASMALIG_OPTIONS_HPP

#include <cxxopts.hpp>
#include <lcdot/dotcommand.hpp>
#include <gpid/gpid.hpp>

/* ===== Structures ===== */

struct OptionStorage : public gpid::GPiDOptions {
    gpid::MasmaligOptions mopts;
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
	    ("s,source", "SMTLibv2 File Source",
             cxxopts::value<std::vector<std::string>>(opts.mopts.source_files))
	    ;

        parser.add_options("Engine")
            ("time-limit", "Maximal generation time allowed (seconds)", cxxopts::value<uint64_t>())
            ("p,production-rule", "Production rule identifier for literal generation",
             cxxopts::value<std::vector<std::string>>(opts.mopts.targets))
            ("list-production-rules", "List the production rules available", cxxopts::value<bool>())
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
        std::vector<std::string> help_cats = {"", "Input", "Engine"};
	if (results.count("help")) {
	    snlog::l_message(parser.help(help_cats));
	    return OptionStatus::ENDED;
	}
	if (results.count("version")) {
	    snlog::l_message(gpid::version_message);
	    return OptionStatus::ENDED;
	}

        if (results.count("list-production-rules")) {
            snlog::l_info("Masmalig production rules");
            for (auto r : mlbsmt2::productionDescriptions)
                snlog::l_notif(r.first, r.second);
            return OptionStatus::ENDED;
        }

        // opts.source_files automatically filled

        if (results.count("time-limit"))
            opts.core.time_limit = results["time-limit"].as<uint64_t>();

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
            // { "load-abducibles", "autogen-abducibles" },
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

        return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

#endif
