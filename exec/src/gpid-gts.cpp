#define GPID_EXEC_GPID_GTS_CPP

#include <iostream>

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
    opts.control.time.registerTime("start");

    generate(opts);

    opts.control.time.registerTime("end");

#ifdef GPID_INSTRUMENTATION
    instrument::finalize(opts.instrument, ictrl);
#endif

    l_message("print generation statistics...");
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic
        ("Total time", opts.control.time.milliseconds("start", "end"));
    opts.control.stats.addStatistic
        ("Generation time", opts.control.time.milliseconds("generation", "generation-end"), 4);
    l_raw(opts.control.stats);

    l_message("complete.");
    return EXIT_SUCCESS;
}
