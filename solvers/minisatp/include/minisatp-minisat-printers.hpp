#ifndef MINISAT_PATCHED_MINISAT_PRE_PRINTERS_FOR_GPID__HPP
#define MINISAT_PATCHED_MINISAT_PRE_PRINTERS_FOR_GPID__HPP

#include <iostream>
#include <minisat/simp/SimpSolver.h>

namespace gpid {

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
        for (int i = 0; i < c.size(); ++i) out << c[i] << " ";
        return out;
    }

    extern inline
    void p_implicate(std::ostream& out, Minisat::vec<Minisat::Lit>& impl, bool negate) {
        out << "> ";
        for (int i = 0; i < impl.size(); ++i) out << (negate ? ~impl[i] : impl[i]) << " ";
        out << std::endl;
    }

}

#endif
