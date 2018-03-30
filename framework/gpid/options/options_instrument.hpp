/**
 * \file gpid/options/options_instrument.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__OPTIONS__INSTRUMENT_HPP
#define GPID_FRAMEWORK__OPTIONS__INSTRUMENT_HPP

#include <string>

namespace gpid {
namespace instrument {

    /** \brief Options for instrument related utilities. \ingroup gpidinstrumentlib */
    struct InstrumentOptions {

        /** Compile graphs generated via instrumentation to svg directly */
        bool autocompile_graphs = false;

        /** Generate an hypotheses selection graph */
        bool selection_graph = false;
        /** File target of the selection graph if selection_graph == true */
        std::string selection_graph_file;

        /** Generate a webtrace of the execution */
        bool webtrace = false;
        /** File target for the webtrace if webtrace == true */
        std::string webtrace_file;

    };

}
};

#endif
