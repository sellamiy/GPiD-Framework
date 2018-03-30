#ifndef GPID_MINISAT_CONTEXT_SPP
#define GPID_MINISAT_CONTEXT_SPP

#include <sstream>
#include <minisat/simp/SimpSolver.h>

#ifdef MERGE_MINISAT_WRAPPERS
namespace Minisat {
#else
namespace gpid {
#endif
    extern inline std::ostream& operator<<(std::ostream& out, const Minisat::Lit p);
}

namespace gpid {

    struct MinisatContextManager { };

    struct MinisatDeclarations {
        int nVars = 0;
        inline void newVar() { ++nVars; }
    };

    typedef Minisat::Lit MinisatInternal;

    struct MinisatHypothesis {
        const MinisatInternal lit;
        MinisatHypothesis(MinisatInternal d) : lit(d) {}
        MinisatHypothesis(const MinisatHypothesis& d) : lit(d.lit) {}

        inline const std::string str() const {
            std::stringstream result; result << lit; return result.str();
        }
    };

    struct MinisatModelWrapper {
        const Minisat::vec<Minisat::lbool>& model;
        MinisatModelWrapper(Minisat::vec<Minisat::lbool>& m) : model(m) {}
        inline bool isSkippable(MinisatHypothesis& hypothesis) const {
            return model[Minisat::var(hypothesis.lit)] ==
                (sign(hypothesis.lit) ? Minisat::l_False : Minisat::l_True);
        }
    };

}

#endif
