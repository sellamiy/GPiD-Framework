#ifndef LIB_WHY3CPP__SHAPE_DETECTION__HEADER
#define LIB_WHY3CPP__SHAPE_DETECTION__HEADER

#include <map>
#include <vector>
#include <why3cpp/why3config.hpp>

namespace why3cpp {

    struct VCShape {
        const std::string expl;
        const std::vector<std::string> ksources;
        VCShape(const std::string& expl) : expl(expl) {}
        VCShape(const std::string& expl, const std::vector<std::string>& ksources) : expl(expl), ksources(ksources) {}
        VCShape(const VCShape& o) : expl(o.expl), ksources(o.ksources) {}
    };

    using ProblemShape = std::map<size_t, VCShape>;

    extern ProblemShape parse_shape_data(const std::string& shapedata);

    extern ProblemShape detect_shape(const std::string& filename);

}

#endif
