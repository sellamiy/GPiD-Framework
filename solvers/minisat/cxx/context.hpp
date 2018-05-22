#ifndef GPID_MINISAT_CONTEXT_SPP
#define GPID_MINISAT_CONTEXT_SPP

#include <sstream>
#include <minisat/simp/SimpSolver.h>

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

namespace gpid {

    struct MinisatContextManager { };

    struct MinisatDeclarations {
        int nVars = 0;
        inline void newVar() { ++nVars; }
    };

    typedef Minisat::Lit MinisatInternal;

    struct MinisatLiteral {
        const MinisatInternal lit;
        MinisatLiteral(MinisatInternal d) : lit(d) {}
        MinisatLiteral(const MinisatLiteral& d) : lit(d.lit) {}

        inline const std::string str() const {
            std::stringstream result; result << lit; return result.str();
        }
    };

    struct MinisatModelWrapper {
        const Minisat::vec<Minisat::lbool>& model;
        MinisatModelWrapper(Minisat::vec<Minisat::lbool>& m) : model(m) {}
        inline bool isSkippable(MinisatLiteral& literal) const {
            return model[Minisat::var(literal.lit)] ==
                (sign(literal.lit) ? Minisat::l_False : Minisat::l_True);
        }
    };

}

#endif
