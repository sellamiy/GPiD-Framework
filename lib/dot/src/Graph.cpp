#define LIB_DOT__GRAPH_CPP

#include <dot/Graph.hpp>

using namespace dot;

int Graph::createNode(std::string name, GraphNodeType type) {
    nodes[nextNode] = type;
    node_labels[nextNode] = name;
    return nextNode++;
}

void Graph::createEdge(int src, int tgt, std::string label, GraphEdgeType type) {
    GraphEdge edge(src, tgt);
    edges[edge] = type;
    edge_labels[edge] = label;
}

void Graph::changeNodeType(int id, GraphNodeType type) {
    nodes[id] = type;
}

void Graph::changeEdgeType(int src, int tgt, GraphEdgeType type) {
    GraphEdge edge(src, tgt);
    edges[edge] = type;
}

void Graph::clear() {
    nodes.clear();
    edges.clear();
    node_labels.clear();
    edge_labels.clear();
}

extern std::ostream& dot::operator<<(std::ostream& out, Graph& g) {
    out << "digraph " << g.name << " {" << std::endl;
    for (std::pair<int, GraphNodeType> p : g.nodes)
        writeNode(out, p.first, g.node_labels[p.first], p.second, 4);
    for (std::pair<Graph::GraphEdge, GraphEdgeType> p : g.edges)
        writeEdge(out, p.first.source, p.first.target, g.edge_labels[p.first], p.second, 4);
    return out << "}" << std::endl;
}
