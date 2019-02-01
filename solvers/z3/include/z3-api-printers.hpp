#ifndef Z3_API_PRINTERS_FOR_GPID__HPP
#define Z3_API_PRINTERS_FOR_GPID__HPP

#include <iostream>
#include <z3++.h>

extern inline
void p_implicate(std::ostream& out, z3::context& ctx, const z3::expr_vector& active, bool negate) {
    out << "> ";
    z3::expr pfl(ctx);
    bool pfl_inited = false;
    for (unsigned i = 0; i < active.size(); ++i) {
        if (pfl_inited)
            pfl = pfl && active[i];
        else {
            pfl = active[i];
            pfl_inited = true;
        }
    }
    if (negate) pfl = !pfl;
    out << pfl << std::endl;
}

extern inline
void p_implicate(std::ostream& out, const z3::expr& f, bool negate) {
    out << "> " << (negate ? !f : f) << std::endl;
}

#endif
