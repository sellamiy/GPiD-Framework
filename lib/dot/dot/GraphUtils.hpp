#ifndef LIB_DOT__GRAPH_UTILS_HPP
#define LIB_DOT__GRAPH_UTILS_HPP

#include <string>
#include <iostream>

namespace dot {

    enum DotColor {
        dc_aliceblue, dc_antiquewhite, dc_aqua, dc_aquamarine, dc_azure,
        dc_beige, dc_bisque, dc_black, dc_blanchedalmond, dc_blue,
        dc_blueviolet, dc_brown, dc_burlywood, dc_cadetblue, dc_chartreuse,
        dc_chocolate, dc_coral, dc_cornflowerblue, dc_cornsilk, dc_crimson,
        dc_cyan, dc_darkblue, dc_darkcyan, dc_darkgoldenrod, dc_darkgray,
        dc_darkgreen, dc_darkgrey, dc_darkkhaki, dc_darkmagenta, dc_darkolivegreen,
        dc_darkorange, dc_darkorchid, dc_darkred, dc_darksalmon, dc_darkseagreen,
        dc_darkslateblue, dc_darkslategray, dc_darkslategrey, dc_darkturquoise, dc_darkviolet,
        dc_deeppink, dc_deepskyblue, dc_dimgray, dc_dimgrey, dc_dodgerblue,
        dc_firebrick, dc_floralwhite, dc_forestgreen, dc_fuchsia, dc_gainsboro,
        dc_ghostwhite, dc_gold, dc_goldenrod, dc_gray, dc_grey,
        dc_green, dc_greenyellow, dc_honeydew, dc_hotpink, dc_indianred,
        dc_indigo, dc_ivory, dc_khaki, dc_lavender, dc_lavenderblush,
        dc_lawngreen, dc_lemonchiffon, dc_lightblue, dc_lightcoral, dc_lightcyan,
        dc_lightgoldenrodyellow, dc_lightgray, dc_lightgreen, dc_lightgrey, dc_lightpink,
        dc_lightsalmon, dc_lightseagreen, dc_lightskyblue, dc_lightslategray, dc_lightslategrey,
        dc_lightsteelblue, dc_lightyellow, dc_lime, dc_limegreen, dc_linen,
        dc_magenta, dc_maroon, dc_mediumaquamarine, dc_mediumblue, dc_mediumorchid,
        dc_mediumpurple, dc_mediumseagreen, dc_mediumslateblue, dc_mediumspringgreen, dc_mediumturquoise,
        dc_mediumvioletred, dc_midnightblue, dc_mintcream, dc_mistyrose, dc_moccasin,
        dc_navajowhite, dc_navy, dc_oldlace, dc_olive, dc_olivedrab,
        dc_orange, dc_orangered, dc_orchid, dc_palegoldenrod, dc_palegreen,
        dc_paleturquoise, dc_palevioletred, dc_papayawhip, dc_peachpuff, dc_peru,
        dc_pink, dc_plum, dc_powderblue, dc_purple, dc_red,
        dc_rosybrown, dc_royalblue, dc_saddlebrown, dc_salmon, dc_sandybrown,
        dc_seagreen, dc_seashell, dc_sienna, dc_silver, dc_skyblue,
        dc_slateblue, dc_slategray, dc_slategrey, dc_snow, dc_springgreen,
        dc_steelblue, dc_tan, dc_teal, dc_thistle, dc_tomato,
        dc_turquoise, dc_violet, dc_wheat, dc_white, dc_whitesmoke,
        dc_yellow, dc_yellowgreen
    };
    extern std::string dotString(DotColor c);

    enum DotShape {
        ds_box, ds_polygon, ds_ellipse, ds_circle, ds_point,
        ds_egg, ds_triangle, ds_plaintext, ds_diamond,
        ds_trapezium, ds_parallelogram, ds_house, ds_pentagon,
        ds_hexagon, ds_septagon, ds_octagon,
        ds_doublecircle, ds_doubleoctagon, ds_tripleoctagon,
        ds_invtriangle, ds_invtrapezium,
        ds_invhouse, ds_Mdiamond, ds_Msquare, ds_Mcircle,
        ds_rect, ds_rectangle, ds_none, ds_note, ds_tab,
        ds_box3d, ds_component
    };
    extern std::string dotString(DotShape s);

    enum DotArrowType {
        dat_normal, dat_inv, dat_dot, dat_invdot, dat_odot,
        dat_invodot, dat_none, dat_tee, dat_empty, dat_invempty,
        dat_diamond, dat_odiamond, dat_ediamond, dat_crow,
        dat_box, dat_obox, dat_open, dat_halfopen, dat_vee
    };
    extern std::string dotString(DotArrowType t);

    enum DotArrowDir { dad_forward, dad_back, dad_both, dad_none };
    extern std::string dotString(DotArrowDir d);

    enum DotArrowStyle { das_dashed, das_dotted, das_solid };
    extern std::string dotString(DotArrowStyle s);

    class GraphNodeType {
        DotColor gColor, tColor, fColor;
        DotShape shape;
        bool filled, diagonals, rounded;
    public:
        GraphNodeType(const GraphNodeType& t):
            gColor(t.gColor), tColor(t.tColor), fColor(t.fColor), shape(t.shape),
            filled(t.filled), diagonals(t.diagonals), rounded(t.rounded)
        {}
        GraphNodeType(DotColor gColor=DotColor::dc_black,
                      DotColor tColor=DotColor::dc_black,
                      DotColor fColor=DotColor::dc_white,
                      DotShape shape=DotShape::ds_box,
                      bool filled=false, bool diagonals=false, bool rounded=false):
            gColor(gColor), tColor(tColor), fColor(fColor), shape(shape),
            filled(filled), diagonals(diagonals), rounded(rounded)
        {}
        std::string operator()(const std::string label);
    };

    class GraphEdgeType {
        DotColor color;
        DotArrowType aHead, aTail;
        DotArrowDir dir;
        DotArrowStyle style;
    public:
        GraphEdgeType(const GraphEdgeType& t):
            color(t.color), aHead(t.aHead), aTail(t.aTail),
            dir(t.dir), style(t.style)
        {}
        GraphEdgeType(DotColor color=DotColor::dc_black,
                      DotArrowType aHead=DotArrowType::dat_normal,
                      DotArrowType aTail=DotArrowType::dat_normal,
                      DotArrowDir dir=DotArrowDir::dad_forward,
                      DotArrowStyle style=DotArrowStyle::das_solid):
            color(color), aHead(aHead), aTail(aTail),
            dir(dir), style(style)
        {}
        std::string operator()(const std::string label);
    };

    extern void writeNode(std::ostream& stream, int nodeid,
                          const std::string nodelabel, GraphNodeType nodet,
                          int pad=0);
    extern void writeEdge(std::ostream& stream, int srcid, int tgtid,
                          const std::string edgelabel, GraphEdgeType et, int pad=0);

}

#endif
