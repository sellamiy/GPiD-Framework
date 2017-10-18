#ifndef GPID_Z3_OUTPUT_HANDLING_HPP
#define GPID_Z3_OUTPUT_HANDLING_HPP

#include <iostream>
#include <snlog/snlog.hpp>
#include <gpid/config.hpp>
#include <gpid/smt/z3_engine.hpp>

/* Gpid Z3 integr. output printers */
namespace gpid {

    extern inline
    void p_implicate(std::ostream& out, z3::context& ctx, const z3::expr_vector& active, bool negate) {
        out << "> ";
        z3::expr pfl(ctx);
        bool pfl_inited = false;
        for (unsigned i = 1 /* HACK, see below */; i < active.size(); ++i) {
            /* HACK: Assertion 1 considered to be the original problem,
               It is thus not part the abducible.
               This is very very very unsafe. */
            // TODO : Fixme : Sanitize Hack !
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
