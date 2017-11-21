#ifndef GPID_FRAMEWORK__INSTRUMENT__SELECTION_GRAPH_HPP
#define GPID_FRAMEWORK__INSTRUMENT__SELECTION_GRAPH_HPP

#include <cstdint>
#include <string>
#include <stack>
#include <dot/dotgraph.hpp>

namespace gpid {
namespace instrument {

    class SelectionGrapher {
        
        std::ostream& target;
        dot::Graph graph;
        std::stack<int> nstack;
        int temp_node;
        int order;
    public:
        SelectionGrapher(std::ostream& target)
            : target(target), graph("selectionGraph") {}

        void selection(uint32_t id);
        void skip(uint32_t id, std::string reason);
        void confirmSelection();
        void backtrackSelection();
        void implicateDetected();

        void initialize();
        void terminate();
    };

}
}

#endif
