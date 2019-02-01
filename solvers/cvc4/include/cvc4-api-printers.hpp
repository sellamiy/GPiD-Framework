#ifndef CVC4_API_PRINTERS_FOR_GPID__HPP
#define CVC4_API_PRINTERS_FOR_GPID__HPP

#include <iostream>

extern inline
void p_implicate(std::ostream& out, CVC4::ExprManager& em,
                 const std::vector<CVC4::Expr>& impl, bool negate) {
    out << "> ";
    if (impl.size() == 0) { out << std::endl; return; }
    CVC4::Expr pfl = impl.size() > 1 ? em.mkExpr(CVC4::kind::AND, impl) : impl[0];
    if (negate) pfl = em.mkExpr(CVC4::kind::NOT, pfl);
    out << pfl << std::endl;
}

#endif
