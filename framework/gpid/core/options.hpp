/**
 * \file gpid/core/options.hpp
 * \brief GPiD-Framework Algorithm Options.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__OPTIONS_HPP
#define GPID_FRAMEWORK__CORE__OPTIONS_HPP

#include <cstdint>

namespace gpid {

    /** Generic options all algorithms should offer. */
    struct GPiDCoreOptions {
        /** Timeout */
        uint64_t time_limit = 0;
    };

    /** Base class for aggregating framework options. */
    struct GPiDOptions {
        /** Options every framework part should provide. */
        GPiDCoreOptions core;
    };

}

#endif
