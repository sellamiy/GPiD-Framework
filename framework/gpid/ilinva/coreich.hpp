/**
 * \file gpid/ilinva/coreich.hpp
 * \brief GPiD-Framework Inductive Invariant Generator via Abduction core Iterface handler types.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__ILINVA__CORE_ICH_HPP
#define GPID_FRAMEWORK__ILINVA__CORE_ICH_HPP

namespace gpid {

    struct IchState {
        const bool proven;
        const bool strengthenable;
        IchState(bool proven, bool strengthenable)
            : proven(proven), strengthenable(strengthenable)
        {}
    };

}

#endif
