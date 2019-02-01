#define ABDULOT_FRAMEWORK__INSTRUMENT__SELECTION_GRAPH_CPP

#include <abdulot/instrument/graphs.hpp>

using namespace abdulot;

void instrument::SelectionGrapher::selection(const std::string id) {
    order++;
    temp_node = graph.createNode("", lcdot::types::ClassicUnshapedNode);
    std::string label = id + '(' + std::to_string(order) + ')';
    graph.createEdge(nstack.top(), temp_node, label, lcdot::types::ClassicDottedEdge);
}

void instrument::SelectionGrapher::skip(const std::string id, std::string reason) {
    order++;
    int node = graph.createNode(reason, lcdot::types::ClassicUnshapedNode);
    std::string label = id + '(' + std::to_string(order) + ')';
    graph.createEdge(nstack.top(), node, label, lcdot::types::ClassicDottedEdge);
}

void instrument::SelectionGrapher::confirmSelection() {
    graph.changeNodeType(temp_node, lcdot::types::ClassicDiamondNode);
    graph.changeEdgeType(nstack.top(), temp_node, lcdot::types::ClassicEdge);
    nstack.push(temp_node);
}

void instrument::SelectionGrapher::implicateDetected() {
    graph.changeNodeType(nstack.top(), lcdot::types::GreenDiamondNode);
}

void instrument::SelectionGrapher::backtrackSelection() {
    nstack.pop();
}

void instrument::SelectionGrapher::initialize() {
    graph.clear();
    // TODO: Clear Stack
    order = 0;
    temp_node = graph.createNode("init", lcdot::types::ClassicDiamondNode);
    nstack.push(temp_node);
}

void instrument::SelectionGrapher::terminate() {
    target << graph;
}
