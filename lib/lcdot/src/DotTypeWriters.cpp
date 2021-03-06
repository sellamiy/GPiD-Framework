#define LIB_LCDOT__DOT_TYPE_WRITERS_CPP

#include <lcdot/GraphUtils.hpp>

extern void lcdot::writeNode(std::ostream& stream, int nodeid,
                           const std::string& nodelabel, GraphNodeType nodet,
                           int pad) {
    for (int i = 0; i < pad; i++) stream << ' ';
    stream << nodeid << " " << nodet(nodelabel) << ';' << std::endl;
}

extern void lcdot::writeEdge(std::ostream& stream, int srcid, int tgtid,
                           const std::string& edgelabel, GraphEdgeType et, int pad) {
    for (int i = 0; i < pad; i++) stream << ' ';
    stream << srcid << " -> " << tgtid << " " << et(edgelabel) << ';' << std::endl;
}

std::string lcdot::GraphNodeType::operator()(const std::string& label) const {
    std::string out = "";
    out += '[';
    out += "label=\"" + label + "\",";
    out += "color=" + dotString(gColor) + ',';
    out += "fontcolor=" + dotString(tColor) + ',';
    out += "fillcolor=" + dotString(fColor) + ',';
    out += "shape=" + dotString(shape);
    if (filled || diagonals || rounded) out += ", style=";
    if (filled)    out += "filled ";
    if (diagonals) out += "diagonals ";
    if (rounded)   out += "rounded";
    out += ']';
    return out;
}

std::string lcdot::GraphEdgeType::operator()(const std::string& label) const {
    std::string out = "";
    out += '[';
    out += "label=\"" + label + "\",";
    out += "color=" + dotString(color) + ',';
    out += "arrowhead=" + dotString(aHead) + ',';
    out += "arrowtail=" + dotString(aTail) + ',';
    out += "dir=" + dotString(dir) + ',';
    out += "style=" + dotString(style);
    out += ']';
    return out;
}
