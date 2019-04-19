#define WHY3_WHYML_IPH_FOR_GPID__IPH_SHAPE__CPP

#include <fstream>
#include <abdulot/utils/abducibles-utils.hpp>
#include <why3-shape-detection.hpp>

static const size_t ILLEGAL_BLOCK_DATA = (size_t)(-1);

using namespace abdulot;

static inline bool is_property_bypasser_expl(const std::string& expl) {
    return expl == "expl:loop invariant init";
}

void Why3_ShapeDetector::detectVCShape(const why3cpp::ProofResult& pr) {
    std::map<size_t, std::string>::iterator it = properties_shape.begin();
    bool before_start = true;
    for (auto& expl : pr.getExplanations()) {
        if (is_property_bypasser_expl(why3cpp::expl(expl.second))) {
            if (before_start) {
                before_start = false;
            } else {
                ++it;
                if (it == properties_shape.end()) {
                    snlog::l_warn() << "WhyML shape detector detected more loops"
                                    << " than invariants you have declared"
                                    << snlog::l_end;
                }
            }
        }
        vc_shape[expl.first] = why3cpp::expl(expl.second);
        maxp_shape[expl.first] = it->first;
    }
}

bool Why3_ShapeDetector::canGenerateBlock
(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const {
    const block_t _dum = generateBlock(pr, cached);
    return _dum.first != ILLEGAL_BLOCK_DATA && _dum.second != ILLEGAL_BLOCK_DATA;
}

block_t Why3_ShapeDetector::generateBlock
(const why3cpp::ProofResult& pr, const std::set<block_t>& cached) const {
    // TODO: Perform a better candidacy pruning with a better shape detection
    for (const auto& vcd : vc_shape) {
        if (pr.isProved(vcd.first))
            continue;
        for (const auto& propd : properties_shape) {
            if (propd.first > maxp_shape.at(vcd.first))
                /* Warning: This is based on the assumption that properties
                   identifers follow the same ordering as properties within
                   the source. This should be true.
                   If it is true, then this test gives the result we expect
                   because map iteration done by the detectVCShape is on an
                   std::map with sorted key indices */
                break;
            block_t _dum = block_t(vcd.first, propd.first);
            if (stdutils::ninset(cached, _dum))
                return _dum;
        }
    }
    return block_t(ILLEGAL_BLOCK_DATA, ILLEGAL_BLOCK_DATA);
}
