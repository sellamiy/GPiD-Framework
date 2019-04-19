#ifndef WHY3_WHYML_IPH_FOR_GPID__SHAPE_DETECTION__HPP
#define WHY3_WHYML_IPH_FOR_GPID__SHAPE_DETECTION__HPP

#include <stack>
#include <abdulot/ilinva/iph-core.hpp>
#include "why3-content-wrapper.hpp"

// Maps @block ---> < why3vc-identifier, why3property-identifier >
using block_t = std::pair<size_t, size_t>;

class Why3_ShapeDetector {
    std::map<size_t, std::string> properties_shape;
    std::map<size_t, std::string> vc_shape;
    std::map<size_t, size_t> maxp_shape;
public:
    Why3_ShapeDetector(const Why3_Template& sourcedata) {
        for (size_t pid : sourcedata.getPropertyIds())
            properties_shape[pid] = sourcedata.getProperty(pid).type;
    }

    bool canGenerateBlock(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const;

    block_t generateBlock(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const;

    inline bool isVCShaped() const { return vc_shape.size() > 0; }

    void detectVCShape(const why3cpp::ProofResult& pr);
};

#endif
