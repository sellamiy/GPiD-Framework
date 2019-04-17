/**
 * \file abdulot/ilinva/data-dual.hpp
 * \brief Dual Code-Interface conditions and checker.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__DUAL_DATA_HPP
#define ABDULOT__ILINVA__DUAL_DATA_HPP

#include <abdulot/core/errors.hpp>
#include <abdulot/core/saitypes.hpp>
#include <abdulot/core/memory.hpp>
#include <abdulot/ilinva/options.hpp>

namespace abdulot {
namespace ilinva {

    template<typename ProblemHandlerT, typename InterfaceT, typename InterfaceLiteralBrowser>
    typename ProblemHandlerT::ConstraintT
    convert(const ObjectMapper<typename InterfaceT::LiteralT>& mapper,
            InterfaceLiteralBrowser& cons, typename InterfaceT::ContextManagerT& ctx);

    template<typename ProblemHandlerT, typename InterfaceT>
    typename InterfaceT::LiteralT
    convert(const typename ProblemHandlerT::ConstraintT& ch_c, typename InterfaceT::ContextManagerT& ctx);

    template<typename ProblemHandlerT, typename InterfaceT, typename InterfaceLiteralBrowser>
    class DualConstraintData {
        typename ProblemHandlerT::ConstraintT ch_c;
    public:
        DualConstraintData(typename ProblemHandlerT::ConstraintT cons)
            : ch_c(cons) {}
        DualConstraintData(const ObjectMapper<typename InterfaceT::LiteralT>& mapper,
                           InterfaceLiteralBrowser& cons,
                           typename InterfaceT::ContextManagerT& ctx)
            : ch_c(convert<ProblemHandlerT, InterfaceT, InterfaceLiteralBrowser>(mapper, cons, ctx)) {}
        DualConstraintData(DualConstraintData& o)
            : ch_c(o.ch_c) {}
        inline operator typename ProblemHandlerT::ConstraintT() const { return ch_c; }
    };

}
}

#endif
