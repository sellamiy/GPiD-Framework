/**
 * \file lcdot/TypesLibrary.hpp
 * \author Yanis Sellami
 * \date 2017
 *
 * \brief Definitions of usable nodes and edge types.
 */
#ifndef LIB_LCDOT__TYPES_LIBRARY_HPP
#define LIB_LCDOT__TYPES_LIBRARY_HPP

#include <lcdot/GraphUtils.hpp>

namespace lcdot {
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
    /** \brief Diamond Node (White on Black background) */
    extern const GraphNodeType BlackDiamondNode;

    /** \brief Black straight edge */
    extern const GraphEdgeType ClassicEdge;
    /** \brief Black dashed edge */
    extern const GraphEdgeType ClassicDashedEdge;
    /** \brief Black dotted edge */
    extern const GraphEdgeType ClassicDottedEdge;

}
}

#endif
