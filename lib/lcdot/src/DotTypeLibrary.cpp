#define LIB_LCDOT__DOT_TYPE_LIBRARY_CPP

#include <lcdot/TypesLibrary.hpp>

using namespace lcdot;

extern const GraphNodeType lcdot::types::ClassicBoxNode = GraphNodeType();
extern const GraphNodeType lcdot::types::ClassicUnshapedNode
= GraphNodeType(DotColor::dc_black, DotColor::dc_black, DotColor::dc_white, DotShape::ds_plaintext,
                false, false, false);

extern const GraphNodeType lcdot::types::ClassicDiamondNode
= GraphNodeType(DotColor::dc_black, DotColor::dc_black, DotColor::dc_white, DotShape::ds_diamond,
                false, false, false);
extern const GraphNodeType lcdot::types::RedDiamondNode
= GraphNodeType(DotColor::dc_black, DotColor::dc_black, DotColor::dc_red, DotShape::ds_diamond,
                true, false, false);
extern const GraphNodeType lcdot::types::GreenDiamondNode
= GraphNodeType(DotColor::dc_black, DotColor::dc_black, DotColor::dc_green, DotShape::ds_diamond,
                true, false, false);
extern const GraphNodeType lcdot::types::BlackDiamondNode
= GraphNodeType(DotColor::dc_black, DotColor::dc_white, DotColor::dc_black, DotShape::ds_diamond,
                true, false, false);

extern const GraphEdgeType lcdot::types::ClassicEdge = GraphEdgeType();
extern const GraphEdgeType lcdot::types::ClassicDashedEdge
= GraphEdgeType(DotColor::dc_black, DotArrowType::dat_normal, DotArrowType::dat_normal,
                DotArrowDir::dad_forward, DotArrowStyle::das_dashed);
extern const GraphEdgeType lcdot::types::ClassicDottedEdge
= GraphEdgeType(DotColor::dc_black, DotArrowType::dat_normal, DotArrowType::dat_normal,
                DotArrowDir::dad_forward, DotArrowStyle::das_dotted);
