/**
 * \file abdulot/instrument/graphs.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT_FRAMEWORK__INSTRUMENT__SELECTION_GRAPH_HPP
#define ABDULOT_FRAMEWORK__INSTRUMENT__SELECTION_GRAPH_HPP

#include <cstdint>
#include <stack>
#include <lcdot/dotgraph.hpp>

namespace abdulot {
namespace instrument {

    /**
     * \brief Class for logging and exporting the hypotheses selection graph.
     * \ingroup abdulotinstrumentlib
     */
    class SelectionGrapher {
        
        std::ostream& target;
        lcdot::Graph graph;
        std::stack<int> nstack;
        int temp_node;
        int order;
    public:
        SelectionGrapher(std::ostream& target)
            : target(target), graph("selectionGraph") {}

        void selection(const std::string id);
        void skip(const std::string id, const std::string reason);
        void confirmSelection();
        void backtrackSelection();
        void implicateDetected();

        void initialize();
        void terminate();
    };

}
}

#endif
