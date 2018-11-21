/**
 * \file gpid/ilinva/dual_data.hpp
 * \brief Dual Code-Interface conditions and checker.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__ILINVA__DUAL_DATA_HPP
#define GPID_FRAMEWORK__ILINVA__DUAL_DATA_HPP

#include <gpid/core/errors.hpp>
#include <gpid/core/saitypes.hpp>
#include <gpid/ilinva/options.hpp>

namespace gpid {

    template<typename CodeHandlerT, typename InterfaceT, typename InterfaceLiteralBrowser>
    typename CodeHandlerT::ConstraintT
    convert(const ObjectMapper<typename InterfaceT::LiteralT>& mapper,
            InterfaceLiteralBrowser& cons, typename InterfaceT::ContextManagerT& ctx,
            typename CodeHandlerT::ContextManagerT& ictx);

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
                           typename InterfaceT::ContextManagerT& ctx,
                           typename CodeHandlerT::ContextManagerT& ictx)
            : ch_c(convert<CodeHandlerT, InterfaceT, InterfaceLiteralBrowser>(mapper, cons, ctx, ictx)) {}
        DualConstraintData(DualConstraintData& o)
            : ch_c(o.ch_c) {}
        inline operator typename CodeHandlerT::ConstraintT() const { return ch_c; }
    };

}

#endif
