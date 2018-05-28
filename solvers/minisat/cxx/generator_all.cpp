#ifndef GPID_MINISAT_GENERATOR_ALL_SPP
#define GPID_MINISAT_GENERATOR_ALL_SPP

using namespace snlog;
using namespace Minisat;

namespace gpid {

    static inline uint32_t countAbducibles_all(MinisatContextManager& ctxm, MinisatDeclarations&) {
        return 2*ctxm.nVars;
    }

    static inline void generateAbducibles_all(MinisatContextManager&, MinisatDeclarations&,
                                              LiteralsEngine<MinisatSolverEngine>& set) {
        alloc_gab<MinisatLiteral>(set.getSourceSize());
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            Lit cstl;
            cstl.x = i;
            store_gab_hyp<LiteralsEngine<MinisatSolverEngine>, Lit>(set, i, cstl);
            set.mapLink(i, i%2 == 0 ? i+1 : i-1);
        }
    }

}

#endif
