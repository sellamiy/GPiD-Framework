#ifndef GPID_CVC4_IMPLICATE_PRINTER_SPP
#define GPID_CVC4_IMPLICATE_PRINTER_SPP

#include <iostream>

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

    template<> inline std::ostream& operator<< <CVC4Literal>
    (std::ostream& out, const LiteralHypothesisPrinter<CVC4Literal>& hlp) {
        for (auto lit : hlp.hypothesis) {
            if (hlp.negate) out << " not(";
            else out << " ";
            out << hlp.mapper.get(lit).expr;
            if (hlp.negate) out << ")";
        }
        return out;
    }

};

#endif
