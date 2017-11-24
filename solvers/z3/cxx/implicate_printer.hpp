#ifndef GPID_Z3_IMPLICATE_PRINTER_SPP
#define GPID_Z3_IMPLICATE_PRINTER_SPP

#include <iostream>

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

};

#endif
