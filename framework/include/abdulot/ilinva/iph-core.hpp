/**
 * \file abdulot/ilinva/iph-core.hpp
 * \brief GPiD-Framework Inductive Invariant Generator via Abduction core Iterface handler types.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__CORE_IPH_HPP
#define ABDULOT__ILINVA__CORE_IPH_HPP

namespace abdulot {
namespace ilinva {

    struct IphState {
        const bool proven;
        const bool strengthenable;
        IphState(bool proven, bool strengthenable)
            : proven(proven), strengthenable(strengthenable)
        {}
    };

}
}

#endif
