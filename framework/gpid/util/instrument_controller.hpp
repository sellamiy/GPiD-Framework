#ifndef GPID_CONTROLLER_INSTRUMENTATION_HPP
#define GPID_CONTROLLER_INSTRUMENTATION_HPP

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

    };

}
};

#endif
