#define GPID_SELCTION_GRAPH_INSTR_IMPLEM

#include <gpid/instrument/selection_graph.hpp>

using namespace gpid;

void instrument::SelectionGrapher::selection(uint32_t id) {
    temp_node = graph.createNode("", dot::types::ClassicDiamondNode);
    graph.createEdge(nstack.top(), temp_node, std::to_string(id), dot::types::ClassicDottedEdge);
}

void instrument::SelectionGrapher::skip(uint32_t id, std::string reason) {
    int node = graph.createNode(reason, dot::types::ClassicBoxNode);
    graph.createEdge(nstack.top(), node, std::to_string(id), dot::types::ClassicDottedEdge);
}

void instrument::SelectionGrapher::confirmSelection() {
    graph.changeEdgeType(nstack.top(), temp_node, dot::types::ClassicEdge);
    nstack.push(temp_node);
}

void instrument::SelectionGrapher::backtrackSelection() {
    nstack.pop();
}

void instrument::SelectionGrapher::initialize() {
    graph.clear();
    temp_node = graph.createNode("init", dot::types::ClassicDiamondNode);
}

void instrument::SelectionGrapher::terminate() {
    target << graph;
}
