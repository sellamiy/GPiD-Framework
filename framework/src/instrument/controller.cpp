#define ABDULOT_FRAMEWORK__INSTRUMENT__CONTROLLER_CPP

#include <fstream>
#include <abdulot/instrument/controller.hpp>

using namespace abdulot;

static std::ofstream nullstream;

instrument::InstrumentController::InstrumentController
(const instrument::InstrumentOptions& opts)
{
    if (opts.selection_graph)
        selection_graph_stream = new std::ofstream(opts.selection_graph_file);
    else
        selection_graph_stream = &nullstream;
    if (opts.webtrace)
        webtrace_stream = new std::ofstream(opts.webtrace_file);
    else
        webtrace_stream = &nullstream;
}

instrument::InstrumentController::InstrumentController
(const instrument::InstrumentController& ctrler) :
    selection_graph_stream(ctrler.selection_graph_stream),
    webtrace_stream(ctrler.webtrace_stream)
{ }
