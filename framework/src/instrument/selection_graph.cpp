#define GPID_SELCTION_GRAPH_INSTR_IMPLEM

#include <gpid/instrument/selection_graph.hpp>

using namespace gpid;

void instrument::SelectionGrapher::selection(uint32_t id) {
    order++;
    temp_node = graph.createNode("", dot::types::ClassicUnshapedNode);
    std::string label = std::to_string(id) + '(' + std::to_string(order) + ')';
    graph.createEdge(nstack.top(), temp_node, label, dot::types::ClassicDottedEdge);
}

void instrument::SelectionGrapher::skip(uint32_t id, std::string reason) {
    order++;
    int node = graph.createNode(reason, dot::types::ClassicUnshapedNode);
    std::string label = std::to_string(id) + '(' + std::to_string(order) + ')';
    graph.createEdge(nstack.top(), node, label, dot::types::ClassicDottedEdge);
}

void instrument::SelectionGrapher::confirmSelection() {
    graph.changeNodeType(temp_node, dot::types::ClassicDiamondNode);
    graph.changeEdgeType(nstack.top(), temp_node, dot::types::ClassicEdge);
    nstack.push(temp_node);
}

void instrument::SelectionGrapher::implicateDetected() {
    graph.changeNodeType(nstack.top(), dot::types::GreenDiamondNode);
}

void instrument::SelectionGrapher::backtrackSelection() {
    nstack.pop();
}

void instrument::SelectionGrapher::initialize() {
    graph.clear();
    // TODO: Clear Stack
    order = 0;
    temp_node = graph.createNode("init", dot::types::ClassicDiamondNode);
    nstack.push(temp_node);
}

void instrument::SelectionGrapher::terminate() {
    target << graph;
}
