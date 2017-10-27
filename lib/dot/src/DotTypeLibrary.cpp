#ifndef _DOT_TYPES_LIBRARY_
#define _DOT_TYPES_LIBRARY_

#include <dot/TypesLibrary.hpp>

using namespace dot;

extern const GraphNodeType dot::types::ClassicBoxNode = GraphNodeType();
extern const GraphNodeType dot::types::ClassicDiamondNode
= GraphNodeType(DotColor::dc_black, DotColor::dc_black, DotColor::dc_white, DotShape::ds_diamond,
                false, false, false);

extern const GraphEdgeType dot::types::ClassicEdge = GraphEdgeType();
extern const GraphEdgeType dot::types::ClassicDashedEdge
= GraphEdgeType(DotColor::dc_black, DotArrowType::dat_normal, DotArrowType::dat_normal,
                DotArrowDir::dad_forward, DotArrowStyle::das_dashed);
extern const GraphEdgeType dot::types::ClassicDottedEdge
= GraphEdgeType(DotColor::dc_black, DotArrowType::dat_normal, DotArrowType::dat_normal,
                DotArrowDir::dad_forward, DotArrowStyle::das_dotted);

#endif
