#define LIB_LCDOT__DOT_TYPE_TABLES_CPP

#include <lcdot/GraphUtils.hpp>

namespace lcdot {
namespace tables {

    static std::string dotColorTable[] = {
        "aliceblue", "antiquewhite", "aqua", "aquamarine", "azure",
        "beige", "bisque", "black", "blanchedalmond", "blue",
        "blueviolet", "brown", "burlywood", "cadetblue", "chartreuse",
        "chocolate", "coral", "cornflowerblue", "cornsilk", "crimson",
        "cyan", "darkblue", "darkcyan", "darkgoldenrod", "darkgray",
        "darkgreen", "darkgrey", "darkkhaki", "darkmagenta", "darkolivegreen",
        "darkorange", "darkorchid", "darkred", "darksalmon", "darkseagreen",
        "darkslateblue", "darkslategray", "darkslategrey", "darkturquoise", "darkviolet",
        "deeppink", "deepskyblue", "dimgray", "dimgrey", "dodgerblue",
        "firebrick", "floralwhite", "forestgreen", "fuchsia", "gainsboro",
        "ghostwhite", "gold", "goldenrod", "gray", "grey",
        "green", "greenyellow", "honeydew", "hotpink", "indianred",
        "indigo", "ivory", "khaki", "lavender", "lavenderblush",
        "lawngreen", "lemonchiffon", "lightblue", "lightcoral", "lightcyan",
        "lightgoldenrodyellow", "lightgray", "lightgreen", "lightgrey", "lightpink",
        "lightsalmon", "lightseagreen", "lightskyblue", "lightslategray", "lightslategrey",
        "lightsteelblue", "lightyellow", "lime", "limegreen", "linen",
        "magenta", "maroon", "mediumaquamarine", "mediumblue", "mediumorchid",
        "mediumpurple", "mediumseagreen", "mediumslateblue", "mediumspringgreen", "mediumturquoise",
        "mediumvioletred", "midnightblue", "mintcream", "mistyrose", "moccasin",
        "navajowhite", "navy", "oldlace", "olive", "olivedrab",
        "orange", "orangered", "orchid", "palegoldenrod", "palegreen",
        "paleturquoise", "palevioletred", "papayawhip", "peachpuff", "peru",
        "pink", "plum", "powderblue", "purple", "red",
        "rosybrown", "royalblue", "saddlebrown", "salmon", "sandybrown",
        "seagreen", "seashell", "sienna", "silver", "skyblue",
        "slateblue", "slategray", "slategrey", "snow", "springgreen",
        "steelblue", "tan", "teal", "thistle", "tomato",
        "turquoise", "violet", "wheat", "white", "whitesmoke",
        "yellow", "yellowgreen"
    };

    static std::string dotShapeTable[] = {
        "box", "polygon", "ellipse", "circle", "point", "egg", "triangle", "plaintext", "diamond",
        "trapezium", "parallelogram", "house", "pentagon", "hexagon", "septagon", "octagon",
        "doublecircle", "doubleoctagon", "tripleoctagon", "invtriangle", "invtrapezium",
        "invhouse", "Mdiamond", "Msquare", "Mcircle", "rect", "rectangle", "none", "note", "tab",
        "box3d", "component"
    };

    static std::string dotArrowTypeTable[] = {
        "normal", "inv", "dot", "invdot", "odot", "invodot", "none", "tee",
        "empty", "invempty", "diamond", "odiamond", "ediamond", "crow",
        "box", "obox", "open", "halfopen", "vee"
    };

    static std::string dotArrowDirTable[] = {
        "forward", "back", "both", "none"
    };

    static std::string dotArrowStyleTable[] = {
        "dashed", "dotted", "solid"
    };
    
}
}

extern std::string lcdot::dotString(DotColor c) {
    return tables::dotColorTable[c];
}
extern std::string lcdot::dotString(DotShape s) {
    return tables::dotShapeTable[s];
}
extern std::string lcdot::dotString(DotArrowType t) {
    return tables::dotArrowTypeTable[t];
}
extern std::string lcdot::dotString(DotArrowDir d) {
    return tables::dotArrowDirTable[d];
}
extern std::string lcdot::dotString(DotArrowStyle s) {
    return tables::dotArrowStyleTable[s];
}
