#ifndef GPID_FRAMEWORK__IMPGEN__SKIP_CONTROL_HPP
#define GPID_FRAMEWORK__IMPGEN__SKIP_CONTROL_HPP

#include <gpid/impgen/options.hpp>

namespace gpid {

    struct SkipController {
        SkipController(const ImpgenOptions& opts);
        SkipController(const SkipController& ctrler);

        const bool storage;
        const uint32_t max_level;
        const bool inconsistencies;
        const bool consequences;
    };

};

#endif
