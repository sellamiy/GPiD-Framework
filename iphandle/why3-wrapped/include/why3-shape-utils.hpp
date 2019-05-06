#ifndef WHY3_WHYML_IPH_FOR_GPID__SHAPE_UTILS__HPP
#define WHY3_WHYML_IPH_FOR_GPID__SHAPE_UTILS__HPP

#include <string>
#include <why3cpp/why3shape.hpp>
#include "why3-expl-utils.hpp"

static inline bool mayRequireInitStrengthening(const why3cpp::ProblemShape& shape) {
    size_t init_count = 0;
    for (const auto& ppair : shape)
        if (isInitExplanation(ppair.second.expl))
            ++init_count;
    return init_count > 1;
}

#endif
