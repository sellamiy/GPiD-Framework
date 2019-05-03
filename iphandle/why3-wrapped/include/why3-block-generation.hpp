#ifndef WHY3_WHYML_IPH_FOR_GPID__BLOCK_GENERATION__HPP
#define WHY3_WHYML_IPH_FOR_GPID__BLOCK_GENERATION__HPP

#include <stack>
#include <why3cpp/why3shape.hpp>
#include <abdulot/ilinva/iph-core.hpp>
#include "why3-content-wrapper.hpp"

// Maps @block ---> < why3vc-identifier, why3property-identifier >
using block_t = std::pair<size_t, size_t>;

class Why3_BlockGenerator {
    std::map<size_t, std::string> properties_shape;
    const why3cpp::ProblemShape& vc_shape;
    std::map<size_t, size_t> maxp_shape;
public:
    Why3_BlockGenerator(const why3cpp::ProblemShape& vc_shape, const Why3_Template& sourcedata);

    bool canGenerateBlock(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const;

    block_t generateBlock(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const;
};

#endif
