#ifndef GPID_CVC4_OUTPUT_HANDLING_HPP
#define GPID_CVC4_OUTPUT_HANDLING_HPP

#include <iostream>
#include <snlog/snlog.hpp>
#include <gpid/config.hpp>
#include <gpid/smt/cvc4_engine.hpp>

/* Gpid CVC4 integr. output printers */
namespace gpid {

    extern inline
    void p_implicate(std::ostream& out, CVC4::ExprManager& em,
                     const std::vector<CVC4::Expr>& impl, bool negate) {
        out << "> ";
        CVC4::Expr pfl = em.mkExpr(CVC4::kind::AND, impl);
        if (negate) pfl = em.mkExpr(CVC4::kind::NOT, pfl);
        out << pfl << std::endl;
    }

};

#endif
