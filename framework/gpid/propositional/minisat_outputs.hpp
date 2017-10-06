#ifndef GPID_MINISAT_OUTPUT_HANDLING_HPP
#define GPID_MINISAT_OUTPUT_HANDLING_HPP

#include <iostream>
#include <snlog/snlog.hpp>
#include <gpid/config.hpp>
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

    extern inline std::ostream& operator<<(std::ostream& out, const Minisat::lbool p) {
        return out << (p == Minisat::l_Undef ? "U" : p == Minisat::l_True ? "T" : "F");
    }

    extern inline std::ostream& operator<<(std::ostream& out, const Minisat::vec<Minisat::lbool>& m) {
        out << "< ";
        for (int i = 0; i < m.size(); ++i) out << m[i] << " ";
        return out << ">";
    }

    extern inline std::ostream& operator<<(std::ostream& out, const Minisat::vec<Minisat::Lit>& c) {
        out << "< ";
        for (int i = 0; i < c.size(); ++i) out << c[i] << " ";
        return out << ">";
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

    extern inline std::ostream& operator<<(std::ostream& out, const std::vector<MinisatHypothesis>& c) {
        out << "< ";
        for (MinisatHypothesis hyp : c) out << hyp.lit << " ";
        return out << ">";
    }

    extern inline
    void p_implicate(std::ostream& out, std::vector<MinisatHypothesis>& impl, bool negate) {
        out << "> ";
        for (MinisatHypothesis hyp : impl) out << (negate ? ~(hyp.lit) : hyp.lit) << " ";
        out << std::endl;
    }

};

#endif
