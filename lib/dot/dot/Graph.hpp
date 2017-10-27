#ifndef _DOT_GRAPH_HEADER_
#define _DOT_GRAPH_HEADER_

#include <map>
#include <dot/GraphUtils.hpp>

namespace dot {

    class Graph {
        struct GraphEdge {
            const int source, target;
            GraphEdge(int source, int target):
                source(source), target(target) {}
            GraphEdge(const GraphEdge& e):
                source(e.source), target(e.target) {}
        };
        struct GraphEdgeCompare {
            inline bool operator() (const GraphEdge& e1, const GraphEdge& e2) const {
                return (std::to_string(e1.source) + " <|> " + std::to_string(e1.target))
                    <  (std::to_string(e2.source) + " <|> " + std::to_string(e2.target));
            }
        };

        std::string name;
        int nextNode;
        std::map<int, std::string> node_labels;
        std::map<int, GraphNodeType> nodes;
        std::map<GraphEdge, std::string, GraphEdgeCompare> edge_labels;
        std::map<GraphEdge, GraphEdgeType, GraphEdgeCompare> edges;
    public:
        Graph(std::string name) : name(name), nextNode(0) {}

        int createNode(std::string name, GraphNodeType type);
        void createEdge(int src, int tgt, std::string label, GraphEdgeType type);
        void changeNodeType(int id, GraphNodeType type);
        void changeEdgeType(int src, int tgt, GraphEdgeType type);

        void clear();

        friend std::ostream& operator<<(std::ostream& out, Graph& g);
    };
    extern std::ostream& operator<<(std::ostream& out, Graph& g);

}

#endif
