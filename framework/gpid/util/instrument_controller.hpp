#ifndef GPID_FRAMEWORK__UTIL__INSTRUMENT_CONTROLLER_HPP
#define GPID_FRAMEWORK__UTIL__INSTRUMENT_CONTROLLER_HPP

#include <iostream>
#include <gpid/config.hpp>
#include <gpid/options/options_instrument.hpp>

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
};

#endif
