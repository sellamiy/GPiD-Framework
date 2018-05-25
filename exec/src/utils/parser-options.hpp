#ifndef GPID_EXEC__UTILS__PARSER_OPTIONS_HPP
#define GPID_EXEC__UTILS__PARSER_OPTIONS_HPP

#include <cxxopts.hpp>
#include <gpid/gpid.hpp>

/* ===== Structures ===== */

struct ParserOptions {
    std::string input;
};

enum class OptionStatus {
    OK, ENDED, FAILURE
};

static inline OptionStatus parseOptions(ParserOptions& opts, int argc, const char** argv);
static inline OptionStatus handleOptions
(ParserOptions& opts, cxxopts::Options& parser, cxxopts::ParseResult& results);

/* ===== Parser ===== */

static inline OptionStatus parseOptions(ParserOptions& opts, int argc, const char** argv) {
    try {

	cxxopts::Options parser(argv[0], gpid::project_full_name + "--parser");

	parser.add_options()
	    ("h,help", "Print this help message")
	    ("v,version", "Print framework version")
	    ;

	parser.add_options("Input")
	    ("i,input", "Input file", cxxopts::value<std::string>())
	    ;

	cxxopts::ParseResult results = parser.parse(argc, argv);

	return handleOptions(opts, parser, results);

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

/* ===== Handler ===== */

static inline OptionStatus handleOptions
(ParserOptions& opts, cxxopts::Options& parser, cxxopts::ParseResult& results) {
    try {

	if (results.count("help")) {
	    snlog::l_message(parser.help({"", "Input"}));
	    return OptionStatus::ENDED;
	}
	if (results.count("version")) {
	    snlog::l_message(gpid::generate_version_message());
	    return OptionStatus::ENDED;
	}

	if (results.count("input")) {
	    opts.input = results["input"].as<std::string>();
	} else {
	    snlog::l_fatal("No input file provided");
	    snlog::l_info(parser.help({"Input"}));
	    return OptionStatus::FAILURE;
	}

	return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}

#endif
