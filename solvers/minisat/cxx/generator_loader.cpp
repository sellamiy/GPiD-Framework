#ifndef GPID_MINISAT_GENERATOR_LOADER_SPP
#define GPID_MINISAT_GENERATOR_LOADER_SPP

using namespace snlog;
using namespace Minisat;

namespace gpid {

    static inline void loadAbducible
    (int idx, const std::string abducible,
     MinisatContextManager&, MinisatDeclarations&,
     HypothesesEngine<MinisatSolver>& set, std::map<int,int>& linker) {
        int lit_data = std::stoi(abducible);
        int lit_var = abs(lit_data)-1;
        Lit cstl = lit_data > 0 ? mkLit(lit_var) : ~mkLit(lit_var);
        store_gab_hyp<HypothesesEngine<MinisatSolver>, Lit>(set, idx, cstl);
        // Check for literal linkage
        int lit_complement = cstl.x%2 == 0 ? cstl.x+1 : cstl.x-1;
        if (linker.find(lit_complement) == linker.end()) {
            linker[cstl.x] = idx;
        } else {
            set.mapLink(idx, linker[lit_complement]);
            set.mapLink(linker[lit_complement], idx);
        }
    }

}

#endif
