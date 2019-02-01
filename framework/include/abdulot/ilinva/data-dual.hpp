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
#include <abdulot/ilinva/options.hpp>

namespace abdulot {
namespace ilinva {

    template<typename CodeHandlerT, typename InterfaceT, typename InterfaceLiteralBrowser>
    typename CodeHandlerT::ConstraintT
    convert(const ObjectMapper<typename InterfaceT::LiteralT>& mapper,
            InterfaceLiteralBrowser& cons, typename InterfaceT::ContextManagerT& ctx);

    template<typename CodeHandlerT, typename InterfaceT>
    typename InterfaceT::LiteralT
    convert(const typename CodeHandlerT::ConstraintT& ch_c, typename InterfaceT::ContextManagerT& ctx);

    template<typename CodeHandlerT, typename InterfaceT, typename InterfaceLiteralBrowser>
    class DualConstraintData {
        typename CodeHandlerT::ConstraintT ch_c;
    public:
        DualConstraintData(typename CodeHandlerT::ConstraintT cons)
            : ch_c(cons) {}
        DualConstraintData(const ObjectMapper<typename InterfaceT::LiteralT>& mapper,
                           InterfaceLiteralBrowser& cons,
                           typename InterfaceT::ContextManagerT& ctx)
            : ch_c(convert<CodeHandlerT, InterfaceT, InterfaceLiteralBrowser>(mapper, cons, ctx)) {}
        DualConstraintData(DualConstraintData& o)
            : ch_c(o.ch_c) {}
        inline operator typename CodeHandlerT::ConstraintT() const { return ch_c; }
    };

}
}

#endif
