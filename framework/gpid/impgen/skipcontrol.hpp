/**
 * \file gpid/impgen/skipcontrol.hpp
 * \brief Implicate generator candidate skipping control.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__IMPGEN__SKIP_CONTROL_HPP
#define GPID_FRAMEWORK__IMPGEN__SKIP_CONTROL_HPP

#include <gpid/impgen/options.hpp>

namespace gpid {

    /** Utility class for controlling literal candidates skips. */
    struct SkipController {
        /** Configure the controller. */
        SkipController(const ImpgenOptions& opts);
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
    };

};

#endif
