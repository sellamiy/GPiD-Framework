#define GPID_EXEC_GPID_GTS_CPP

#include "utils/gts-executors.hpp"

using namespace std;
using namespace snlog;
using namespace gpid;

int main(int argc, const char** argv) {
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

    gtsExecutionStatus gStatus = generate(opts);

    opts.control.time.registerTime("end");

#ifdef GPID_INSTRUMENTATION
    instrument::finalize(opts.instrument, ictrl);
#endif

    l_message("print generation statistics...");
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic
        ("Total time", opts.control.time.duration("start", "end"));
    opts.control.stats.addStatistic
        ("Generation time", opts.control.time.duration("generation", "generation-end"), 4);
    l_raw(opts.control.stats);

    l_message("complete.");
    t_error(gStatus != GTS_SUCCESS, "errors occured!");
    return gStatus == GTS_SUCCESS ? EXIT_SUCCESS : EXIT_FAILURE;
}
