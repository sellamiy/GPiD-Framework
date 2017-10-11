#define GPID_GTS_PI_GENERATOR

#include <iostream>
#include <gpid/gpid.hpp>

#include "utils/options_parser.hpp"
#include "utils/executors.hpp"

using namespace std;
using namespace snlog;
using namespace gpid;

int main(int argc, char** argv) {
    OptionStorage opts;
    OptionStatus status = parseOptions(opts, argc, argv);
    if (status == OptionStatus::FAILURE) {
	return EXIT_FAILURE;
    } else if (status == OptionStatus::ENDED) {
	return EXIT_SUCCESS;
    }

    l_message("start implicate generator...");

    switch (opts.generator) {
    case TRUE_SOLVER:
        generate_true_solver(opts);
        break;
    case MINISAT:
        generate_minisat(opts);
        break;
    default:
        l_internal("Got start access to unknown generator");
        return EXIT_FAILURE;
    }

    l_message("complete.");
    return EXIT_SUCCESS;
}
