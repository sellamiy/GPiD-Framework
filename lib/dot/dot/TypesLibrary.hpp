#ifndef LIB_DOT__TYPES_LIBRARY_HPP
#define LIB_DOT__TYPES_LIBRARY_HPP

#include <dot/GraphUtils.hpp>

namespace dot {
namespace types {

    /* node types */
    extern const GraphNodeType ClassicBoxNode;
    extern const GraphNodeType ClassicUnshapedNode;

    extern const GraphNodeType ClassicDiamondNode;
    extern const GraphNodeType RedDiamondNode;
    extern const GraphNodeType GreenDiamondNode;

    /* edge types */
    extern const GraphEdgeType ClassicEdge;
    extern const GraphEdgeType ClassicDashedEdge;
    extern const GraphEdgeType ClassicDottedEdge;

}
}

#endif
