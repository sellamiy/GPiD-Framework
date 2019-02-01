/**
 * \file abdulot/core/options.hpp
 * \brief Abdulot Framework Algorithm Options.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__CORE__OPTIONS_HPP
#define ABDULOT__CORE__OPTIONS_HPP

#include <cstdint>

namespace abdulot {

    /** Generic options all algorithms should offer. */
    struct CoreOptions {
        /** Timeout */
        uint64_t time_limit = 0;
    };

    /** Base class for aggregating framework options. */
    struct AlgorithmOptions {
        /** Options every framework part should provide. */
        CoreOptions core;
    };

}

#endif
