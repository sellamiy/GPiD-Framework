#ifndef GPID_MINISAT_OUTPUT_HANDLING_HPP
#define GPID_MINISAT_OUTPUT_HANDLING_HPP

#include <iostream>
#include <gpid/config.hpp>
#include <gpid/errors.hpp>
#include <gpid/propositional/minisat_pengine.hpp>

/* Strict Minisat output printers */
#ifdef MERGE_MINISAT_OUTPUT_WRAPPERS
namespace Minisat {
#else
namespace gpid {
#endif

    extern inline std::ostream& operator<<(std::ostream& out, const Minisat::Lit p) {
        return out << (p == Minisat::lit_Undef ? "?" : (p.x % 2 == 0 ? "" : "-")) << p.x/2 + 1;
    }

};

/* Gpid Minisat integr. output printers */
namespace gpid {

    extern inline void p_implicate(std::ostream& out, std::vector<MinisatHypothesis>& impl, bool negate) {
        if (negate) {
            out << "> ";
            for (MinisatHypothesis hyp : impl) out << ~(hyp.lit) << " ";
            out << std::endl;
        } else { l_warn("Minisat Implicate Non-negated Printers are not implemeted yet!"); }
    }

};

#endif
