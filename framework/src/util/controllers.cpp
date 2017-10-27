#define GPID_CONTROLLERS_CONSTRUCTORS

#include <fstream>
#include <gpid/util/skipper_controller.hpp>
#include <gpid/util/instrument_controller.hpp>

using namespace gpid;

SkipperController::SkipperController(const CoreOptions& opts) :
    storage(opts.engine.store_implicates)
{ }

SkipperController::SkipperController(const SkipperController& ctrler) :
    storage(ctrler.storage)
{ }

static std::ofstream nullstream;

instrument::InstrumentController::InstrumentController
(const instrument::InstrumentOptions& opts)
{
    if (opts.selection_graph)
        selection_graph_stream = new std::ofstream(opts.selection_graph_file);
    else
        selection_graph_stream = &nullstream;
}

instrument::InstrumentController::InstrumentController
(const instrument::InstrumentController& ctrler) :
    selection_graph_stream(ctrler.selection_graph_stream)
{ }
