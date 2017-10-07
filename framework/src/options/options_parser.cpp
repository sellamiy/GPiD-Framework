#define GPID_OPTIONS_PARSER

#include <vector>
#include <cxxopts/cxxopts.hpp>

#include <snlog/snlog.hpp>

#include <gpid/version.hpp>
#include <gpid/options/options_core.hpp>

namespace gpid {
    static OptionStatus handleOptions(CoreOptions& opts, cxxopts::Options& parser);
};

extern gpid::OptionStatus gpid::parseOptions(CoreOptions& opts, int argc, char** argv) {
    try {

	cxxopts::Options parser(argv[0], project_full_name);

	parser.add_options()
	    ("h,help", "Print this help message")
	    ("v,version", "Print framework version")
	    ;

	parser.add_options("Input")
	    ("i,input", "Input file", cxxopts::value<std::string>())
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

static gpid::OptionStatus gpid::handleOptions(CoreOptions& opts, cxxopts::Options& parser) {
    try {

	if (parser.count("help")) {
	    snlog::l_message(parser.help({"", "Input", "Output"}));
	    return OptionStatus::ENDED;
	}
	if (parser.count("version")) {
	    snlog::l_message(generate_version_message());
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

	return OptionStatus::OK;

    } catch (const cxxopts::OptionException& e) {
	snlog::l_error(e.what());
	return OptionStatus::FAILURE;
    }
}
