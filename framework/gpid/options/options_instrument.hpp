#ifndef GPID_INSTRUMENTATION_OPTIONS_HPP
#define GPID_INSTRUMENTATION_OPTIONS_HPP

#include <string>

namespace gpid {
namespace instrument {

    struct InstrumentOptions {

        bool autocompile_graphs = false;

        bool selection_graph = false;
        std::string selection_graph_file;

    };

}
};

#endif
