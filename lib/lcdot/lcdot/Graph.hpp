/**
 * \file lcdot/Graph.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_LCDOT__GRAPH_HPP
#define LIB_LCDOT__GRAPH_HPP

#include <map>
#include <lcdot/GraphUtils.hpp>

namespace lcdot {

    /** \brief Representation of graphviz-dot graph. */
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
        /** \brief Graph construction. */
        Graph(const std::string& name) : name(name), nextNode(0) {}

        /**
         * \brief Add a node to the graph.
         * \param name Label of the node.
         * \param type Type of the node to create.
         * \return Id of the newly created node.
         */
        int createNode(const std::string& name, GraphNodeType type);
        /**
         * \brief Add an edge to the graph.
         * \param src Id of the source node.
         * \param tgt Id of the destination node.
         * \param label Label of the edge.
         * \param type Type of the edge to create.
         */
        void createEdge(int src, int tgt, const std::string& label, GraphEdgeType type);
        /** \brief Change the type of a node. */
        void changeNodeType(int id, GraphNodeType type);
        /** \brief Change the type of an edge. */
        void changeEdgeType(int src, int tgt, GraphEdgeType type);

        /** \brief Remove all nodes and edges from the graph. */
        void clear();

        friend std::ostream& operator<<(std::ostream& out, Graph& g);
    };

    /** \brief Graph printer utility */
    extern std::ostream& operator<<(std::ostream& out, Graph& g);

}

#endif
