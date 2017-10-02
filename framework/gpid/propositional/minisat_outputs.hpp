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

    extern inline
    void p_implicate(std::ostream& out, Minisat::vec<Minisat::Lit>& impl, bool negate) {
        out << "> ";
        for (int i = 0; i < impl.size(); ++i) out << (negate ? ~impl[i] : impl[i]) << " ";
        out << std::endl;
    }

};

/* Gpid Minisat integr. output printers */
namespace gpid {

    extern inline
    void p_implicate(std::ostream& out, std::vector<MinisatHypothesis>& impl, bool negate) {
        out << "> ";
        for (MinisatHypothesis hyp : impl) out << (negate ? ~(hyp.lit) : hyp.lit) << " ";
        out << std::endl;
    }

};

#endif
