#ifndef GPID_MINISAT_CONTEXT_SPP
#define GPID_MINISAT_CONTEXT_SPP

#include <minisat/simp/SimpSolver.h>

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
