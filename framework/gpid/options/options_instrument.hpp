#ifndef GPID_FRAMEWORK__OPTIONS__INSTRUMENT_HPP
#define GPID_FRAMEWORK__OPTIONS__INSTRUMENT_HPP

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
