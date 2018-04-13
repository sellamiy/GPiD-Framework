#ifndef GPID_FRAMEWORK__SKIPPER_CONTROLLER__PARSERS_HPP
#define GPID_FRAMEWORK__SKIPPER_CONTROLLER__PARSERS_HPP

#include <gpid/options/options_core.hpp>

namespace gpid {

    struct SkipperController {
        SkipperController(const CoreOptions& opts);
        SkipperController(const SkipperController& ctrler);

        const bool storage;
        const uint32_t max_level;
        const bool inconsistencies;
        const bool consequences;
    };

};

#endif
