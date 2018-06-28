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

    class GPiDAlgorithm {
    protected:
        GPiDOptions& options;
        SystemInterruptionFlags iflags;

        virtual void _execute() = 0;

        GPiDAlgorithm(GPiDOptions& o) : options(o) {}
    public:
        using counter_t = uint64_t;

        void execute();
    };

}

#endif
