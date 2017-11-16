#ifndef GPID_CVC4_OUTPUT_HANDLING_HPP
#define GPID_CVC4_OUTPUT_HANDLING_HPP

#include <iostream>
#include <snlog/snlog.hpp>
#include <gpid/config.hpp>
#include <gpid/solvers-wrap/cvc4_engine.hpp>

/* Gpid CVC4 integr. output printers */
namespace gpid {

    extern inline
    void p_implicate(std::ostream& out, CVC4::ExprManager& em,
                     const std::vector<CVC4::Expr>& impl, bool negate) {
        out << "> ";
        if (impl.size() == 0) { out << std::endl; return; }
        CVC4::Expr pfl = impl.size() > 1 ? em.mkExpr(CVC4::kind::AND, impl) : impl[0];
        if (negate) pfl = em.mkExpr(CVC4::kind::NOT, pfl);
        out << pfl << std::endl;
    }

};

#endif
