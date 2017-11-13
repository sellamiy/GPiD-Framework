#ifndef GPID_CONTROLLER_SKIPPER_HPP
#define GPID_CONTROLLER_SKIPPER_HPP

#include <gpid/config.hpp>
#include <gpid/options/options_core.hpp>

namespace gpid {

    struct SkipperController {
        SkipperController(const CoreOptions& opts);
        SkipperController(const SkipperController& ctrler);

        const bool storage;
        const uint32_t max_level;
    };

};

#endif
