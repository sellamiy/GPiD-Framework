#ifndef GPID_MINISAT_MINISAT_PRINTERS_SPP
#define GPID_MINISAT_MINISAT_PRINTERS_SPP

#include <iostream>
#include <gpid/config.hpp>

#ifdef MERGE_MINISAT_WRAPPERS
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

}

#endif
