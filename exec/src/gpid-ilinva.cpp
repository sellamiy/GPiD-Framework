#define GPID_EXEC_GPID_ILINVA_CPP

#include "utils/ilinva-wrappers.hpp"

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

    l_message() << "start implicate generator..." << l_end;
    opts.control.time.registerTime("start");

    ilinvaExecutionStatus gStatus = generate(opts);

    opts.control.time.registerTime("end");

#ifdef GPID_INSTRUMENTATION
    instrument::finalize(opts.instrument, ictrl);
#endif

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic
        ("Total time", opts.control.time.duration("start", "end"));
    if (gStatus == ilinvaExecutionStatus::SUCCESS)
        opts.control.stats.addStatistic
            ("Generation time", opts.control.time.duration("generation", "generation-end"), 4);
    l_message() << "print generation statistics..." << l_end
                << l_raw << opts.control.stats
                << l_message << "complete." << l_end;

    t_error(gStatus != ilinvaExecutionStatus::SUCCESS) << "errors occured!" << l_end;
    return gStatus == ilinvaExecutionStatus::SUCCESS ? EXIT_SUCCESS : EXIT_FAILURE;
}
