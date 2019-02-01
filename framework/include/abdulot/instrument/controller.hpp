/**
 * \file abdulot/instrument/controller.hpp
 * \brief Intrumentation utilities controller.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__INSTRUMENT__CONTROLLER_HPP
#define ABDULOT__INSTRUMENT__CONTROLLER_HPP

#include <iostream>
#include <abdulot/core/config.hpp>
#include <abdulot/instrument/options.hpp>

namespace abdulot {
namespace instrument {

    /** Utility class controlling the algorithmic intrumentations available. */
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
