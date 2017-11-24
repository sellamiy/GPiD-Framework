/**
 * \file dot/TypesLibrary.hpp
 * \author Yanis Sellami
 * \date 2017
 *
 * \brief Definitions of usable nodes and edge types.
 */
#ifndef LIB_DOT__TYPES_LIBRARY_HPP
#define LIB_DOT__TYPES_LIBRARY_HPP

#include <dot/GraphUtils.hpp>

namespace dot {
namespace types {

    /** \brief Box Node (Black on White) */
    extern const GraphNodeType ClassicBoxNode;
    /** \brief Node without borders (Black on White) */
    extern const GraphNodeType ClassicUnshapedNode;

    /** \brief Diamond Node (Black on White) */
    extern const GraphNodeType ClassicDiamondNode;
    /** \brief Diamond Node (Black on Red background) */
    extern const GraphNodeType RedDiamondNode;
    /** \brief Diamond Node (Black on Green background) */
    extern const GraphNodeType GreenDiamondNode;

    /** \brief Black straight edge */
    extern const GraphEdgeType ClassicEdge;
    /** \brief Black dashed edge */
    extern const GraphEdgeType ClassicDashedEdge;
    /** \brief Black dotted edge */
    extern const GraphEdgeType ClassicDottedEdge;

}
}

#endif
