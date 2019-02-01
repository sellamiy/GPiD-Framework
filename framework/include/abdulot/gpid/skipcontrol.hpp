/**
 * \file abdulot/gpid/skipcontrol.hpp
 * \brief Implicate generator candidate skipping control.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__GPID__SKIP_CONTROL_HPP
#define ABDULOT__GPID__SKIP_CONTROL_HPP

#include <abdulot/gpid/options.hpp>

namespace abdulot {
namespace gpid {

    /** Utility class for controlling literal candidates skips. */
    struct SkipController {
        /** Configure the controller. */
        SkipController(const GPiDOptions& opts);
        /** Copy constructor */
        SkipController(const SkipController& ctrler);

        /** Candidates skipped thanks to the storage. */
        const bool storage;
        /** Candidates skipped thanks to depth restrictions. */
        const uint32_t max_level;
        /** Candidates skipped thanks to inconsistancy detection. */
        const bool inconsistencies;
        /** Candidates skipped thanks to consequence detection. */
        const bool consequences;

        const bool additionals;
    };

}
}

#endif
