/**
 * \file abdulot/ilinva/ich-core.hpp
 * \brief GPiD-Framework Inductive Invariant Generator via Abduction core Iterface handler types.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__CORE_ICH_HPP
#define ABDULOT__ILINVA__CORE_ICH_HPP

namespace abdulot {
namespace ilinva {

    struct IchState {
        const bool proven;
        const bool strengthenable;
        IchState(bool proven, bool strengthenable)
            : proven(proven), strengthenable(strengthenable)
        {}
    };

}
}

#endif
