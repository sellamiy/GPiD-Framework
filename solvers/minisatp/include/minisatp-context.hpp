#ifndef MINISAT_PATCHED_CONTEXT_FOR_GPID__HPP
#define MINISAT_PATCHED_CONTEXT_FOR_GPID__HPP

#include <sstream>
#include "minisatp-minisat-printers.hpp"

namespace gpid {

    struct MinisatContextManager {
        int nVars = 0;
        inline void newVar() { ++nVars; }
    };

    struct MinisatDeclarations { };

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
        inline bool implies(MinisatLiteral& literal) const {
            return model[Minisat::var(literal.lit)] ==
                (sign(literal.lit) ? Minisat::l_False : Minisat::l_True);
        }
    };

}

#endif
