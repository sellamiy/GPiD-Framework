#define GPID_EXEC_GPID_IMPGEN_CPP

#include "wrappers.hpp"

using namespace std;
using namespace snlog;

int main(int argc, char** argv) {
    OptionStorage opts;
    OptionStatus status = parseOptions(opts, argc, argv);
    if (status == OptionStatus::FAILURE) {
	return EXIT_FAILURE;
    } else if (status == OptionStatus::ENDED) {
	return EXIT_SUCCESS;
    }

#ifdef INSTRUMENTATION
    abdulot::instrument::InstrumentController ictrl(opts.instrument);
    abdulot::instrument::initialize(opts.instrument, ictrl);
#endif

    l_message() << "start implicate generator..." << l_end;
    opts.control.time.registerTime("start");

    impgenExecutionStatus gStatus = generate(opts);

    opts.control.time.registerTime("end");

#ifdef INSTRUMENTATION
    abdulot::instrument::finalize(opts.instrument, ictrl);
#endif

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic
        ("Total time", opts.control.time.duration("start", "end"));
    opts.control.stats.addStatistic
        ("Generation time", opts.control.time.duration("generation", "generation-end"), 4);
    l_message() << "print generation statistics..."
                << l_raw << opts.control.stats
                << l_message << "complete." << l_end;

    t_error(gStatus != impgenExecutionStatus::SUCCESS) << "errors occured!" << l_end;
    return gStatus == impgenExecutionStatus::SUCCESS ? EXIT_SUCCESS : EXIT_FAILURE;
}
