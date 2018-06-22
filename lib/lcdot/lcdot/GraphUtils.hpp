/**
 * \file lcdot/GraphUtils.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_LCDOT__GRAPH_UTILS_HPP
#define LIB_LCDOT__GRAPH_UTILS_HPP

#include <string>
#include <iostream>

namespace lcdot {

    /** \brief Enumerative representation of graphviz-dot svg graph colors. */
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

    /** \brief Converts a dot color to its graphviz-dot textual form. */
    extern std::string dotString(DotColor c);

    /** \brief Enumerative representation of graphviz-dot graph node shapes. */
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

    /** \brief Converts a node shape to its graphviz-dot textual form. */
    extern std::string dotString(DotShape s);

    /** \brief Enumerative representation of graphviz-dot arrow type. */
    enum DotArrowType {
        dat_normal, dat_inv, dat_dot, dat_invdot, dat_odot,
        dat_invodot, dat_none, dat_tee, dat_empty, dat_invempty,
        dat_diamond, dat_odiamond, dat_ediamond, dat_crow,
        dat_box, dat_obox, dat_open, dat_halfopen, dat_vee
    };

    /** \brief Converts an arrow type to its graphviz-dot textual form. */
    extern std::string dotString(DotArrowType t);

    /** \brief Enumerative representation of graphviz-dot arrow direction. */
    enum DotArrowDir { dad_forward, dad_back, dad_both, dad_none };
    /** \brief Converts an arrow direction to its graphviz-dot textual form. */
    extern std::string dotString(DotArrowDir d);

    /** \brief Enumerative representation of graphviz-dot arrow style. */
    enum DotArrowStyle { das_dashed, das_dotted, das_solid };
    /** \brief Converts an arrow style to its graphviz-dot textual form. */
    extern std::string dotString(DotArrowStyle s);

    /** \brief Representation of a graphviz-dot node format. */
    class GraphNodeType {
        DotColor gColor, tColor, fColor;
        DotShape shape;
        bool filled, diagonals, rounded;
    public:
        /** \brief Copy constructor */
        GraphNodeType(const GraphNodeType& t):
            gColor(t.gColor), tColor(t.tColor), fColor(t.fColor), shape(t.shape),
            filled(t.filled), diagonals(t.diagonals), rounded(t.rounded)
        {}

        /**
         * \brief Node format construction.
         * \param gColor Color of the node borders.
         * \param tColor Color of the node label.
         * \param fColor Background color of the node.
         * \param shape Shape of the node.
         * \param filled Use the background color?
         * \param diagonals Use node diagonals?
         * \param rounded Use rounded corners for the node?
         */
        GraphNodeType(DotColor gColor=DotColor::dc_black,
                      DotColor tColor=DotColor::dc_black,
                      DotColor fColor=DotColor::dc_white,
                      DotShape shape=DotShape::ds_box,
                      bool filled=false, bool diagonals=false, bool rounded=false):
            gColor(gColor), tColor(tColor), fColor(fColor), shape(shape),
            filled(filled), diagonals(diagonals), rounded(rounded)
        {}

        /**
         * \brief Generate graphviz-dot node type for this node.
         * \param label Label given to this node.
         * \return A string representing this node type in dot format.
         */
        std::string operator()(const std::string label);
    };

    /** \brief Representation of a graphviz-dot edge format. */
    class GraphEdgeType {
        DotColor color;
        DotArrowType aHead, aTail;
        DotArrowDir dir;
        DotArrowStyle style;
    public:
        /** \brief Copy constructor */
        GraphEdgeType(const GraphEdgeType& t):
            color(t.color), aHead(t.aHead), aTail(t.aTail),
            dir(t.dir), style(t.style)
        {}

        /**
         * \brief Edge format construction.
         * \param color Color of the edge.
         * \param aHead Type of the arrow for this edge head.
         * \param aTail Type of the arrow for this edge tail.
         * \param dir Direction of the edge.
         * \param style Style of the edge.
         */
        GraphEdgeType(DotColor color=DotColor::dc_black,
                      DotArrowType aHead=DotArrowType::dat_normal,
                      DotArrowType aTail=DotArrowType::dat_normal,
                      DotArrowDir dir=DotArrowDir::dad_forward,
                      DotArrowStyle style=DotArrowStyle::das_solid):
            color(color), aHead(aHead), aTail(aTail),
            dir(dir), style(style)
        {}

        /**
         * \brief Generate graphviz-dot edge type for this edge.
         * \param label Label given to this edge.
         * \return A string representing this edge type in dot format.
         */
        std::string operator()(const std::string label);
    };

    /** \brief Write a node declaration in graphviz-dot format. */
    extern void writeNode(std::ostream& stream, int nodeid,
                          const std::string nodelabel, GraphNodeType nodet,
                          int pad=0);
    /** \brief Write an edge declaration in graphviz-dot format. */
    extern void writeEdge(std::ostream& stream, int srcid, int tgtid,
                          const std::string edgelabel, GraphEdgeType et, int pad=0);

}

#endif
