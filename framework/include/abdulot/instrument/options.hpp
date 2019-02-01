/**
 * \file abdulot/instrument/options.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT_FRAMEWORK__INSTRUMENT__OPTIONS_HPP
#define ABDULOT_FRAMEWORK__INSTRUMENT__OPTIONS_HPP

#include <string>

namespace abdulot {
namespace instrument {

    /** \brief Options for instrument related utilities. \ingroup abdulotinstrumentlib */
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

        /** Local infoline vie instrumentation hooks */
        bool infoliner = false;

    };

}
}

#endif
