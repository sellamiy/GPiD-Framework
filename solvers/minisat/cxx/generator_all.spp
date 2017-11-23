#ifndef GPID_MINISAT_GENERATOR_ALL_SPP
#define GPID_MINISAT_GENERATOR_ALL_SPP

using namespace snlog;
using namespace Minisat;

namespace gpid {

    static inline uint32_t countAbducibles_all(MinisatContextManager&, MinisatDeclarations& decls) {
        return 2*decls.nVars;
    }

    static inline void generateAbducibles_all(MinisatContextManager&, MinisatDeclarations&,
                                              HypothesesSet<MinisatSolver>& set) {
        alloc_gab<MinisatHypothesis>(set.getSourceSize());
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            Lit cstl;
            cstl.x = i;
            store_gab_hyp<HypothesesSet<MinisatSolver>, Lit>(set, i, cstl);
            set.mapLink(i, i%2 == 0 ? i+1 : i-1);
        }
    }

}

#endif
