/**
 * \file gpid/core/algorithm.hpp
 * \brief GPiD-Framework Algorithm Framework.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__ALGORITHM_HPP
#define GPID_FRAMEWORK__CORE__ALGORITHM_HPP

#include <gpid/core/system.hpp>
#include <gpid/core/options.hpp>

namespace gpid {

    /** Base class for algorithmic utilities. */
    class GPiDAlgorithm {
    protected:
        /** Options of the algorithm */
        GPiDOptions& options;
        /** Interruption flags for requesting an interruption */
        SystemInterruptionFlags iflags;

        /** Abstract method for actual algorithm execution. */
        virtual void _execute() = 0;

        /** Algorithm construction and parametrization. */
        GPiDAlgorithm(GPiDOptions& o) : options(o) {}
    public:
        /** Counter type for compting things. */
        using counter_t = uint64_t;

        /** Main wrapper method for executing the algorithm. */
        void execute();
    };

}

#endif
