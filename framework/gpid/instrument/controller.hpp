#ifndef GPID_FRAMEWORK__INSTRUMENT__CONTROLLER_HPP
#define GPID_FRAMEWORK__INSTRUMENT__CONTROLLER_HPP

#include <iostream>
#include <gpid/core/config.hpp>
#include <gpid/instrument/options.hpp>

namespace gpid {
namespace instrument {

    struct InstrumentController {
        InstrumentController(const InstrumentOptions& opts);
        InstrumentController(const InstrumentController& ctrler);

        std::ostream* selection_graph_stream;
        inline std::ostream& getSelectionGraphStream()
        { return *selection_graph_stream; }

        std::ostream* webtrace_stream;
        inline std::ostream& getWebtraceStream()
        { return *webtrace_stream; }

    };

}
}

#endif
