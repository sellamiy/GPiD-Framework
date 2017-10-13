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
                     std::vector<const CVC4Hypothesis>& impl, bool negate) {
        out << "> ";
        CVC4::Expr pfl = em.mkConst(true);
        for (const CVC4Hypothesis hyp : impl) pfl = em.mkExpr(CVC4::kind::AND, pfl, hyp.expr);
        if (negate) pfl = em.mkExpr(CVC4::kind::NOT, pfl);
        out << pfl << std::endl;
    }

};

#endif
