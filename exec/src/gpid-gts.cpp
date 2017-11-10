#define GPID_GTS_PI_GENERATOR

#include <iostream>
#include <gpid/gpid.hpp>

#include "utils/gts-options.hpp"
#include "utils/gts-executors.hpp"

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

#ifdef GPID_INSTRUMENTATION
    instrument::InstrumentController ictrl(opts.instrument);
    instrument::initialize(opts.instrument, ictrl);
#endif

    l_message("start implicate generator...");

    switch (opts.generator) {
    case TRUE_SOLVER:
        generate_true_solver(opts);
        break;
    case MINISAT:
        generate_minisat(opts);
        break;
    case SMT_CVC4:
        generate_cvc4(opts);
        break;
    case SMT_Z3:
        generate_z3(opts);
        break;
    default:
        l_internal("Got start access to unknown generator");
        return EXIT_FAILURE;
    }

#ifdef GPID_INSTRUMENTATION
    instrument::finalize(opts.instrument, ictrl);
#endif

    l_message("print generation statistics...");
    l_raw(opts.control.stats);

    l_message("complete.");
    return EXIT_SUCCESS;
}
