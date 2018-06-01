#ifndef GPID_Z3_IMPLICATE_PRINTER_SPP
#define GPID_Z3_IMPLICATE_PRINTER_SPP

#include <iostream>
#include <gpid/core/wrappers.hpp>

namespace gpid {

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

    template<> inline std::ostream& operator<< <Z3Literal>
    (std::ostream& out, const LiteralHypothesisPrinter<Z3Literal>& hlp) {
        typename LiteralHypothesis<Z3Literal>::iterator it = hlp.hypothesis.begin();
        z3::expr f = hlp.mapper.get(*it).expr;
        while (++it != hlp.hypothesis.end()) {
            f = f && hlp.mapper.get(*it).expr;
        }
        return out << (hlp.negate ? !f : f);
    }

};

#endif
