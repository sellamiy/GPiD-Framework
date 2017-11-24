#ifndef GPID_MINISAT_GENERATOR_LOADER_SPP
#define GPID_MINISAT_GENERATOR_LOADER_SPP

using namespace snlog;
using namespace Minisat;

namespace gpid {

    static inline void loadAbducibles(std::string filename,
                                      MinisatContextManager&, MinisatDeclarations&,
                                      HypothesesSet<MinisatSolver>& set) {
        alloc_gab<MinisatHypothesis>(set.getSourceSize());
        std::map<int, int> linker;
        AbducibleParser parser(filename);
        parser.init();
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            if (!parser.isOk()) {
                l_fatal("Error loading from @file:" + filename);
                break;
            }
            int lit_data = std::stoi(parser.nextAbducible());
            int lit_var = abs(lit_data)-1;
            Lit cstl = lit_data > 0 ? mkLit(lit_var) : ~mkLit(lit_var);
            store_gab_hyp<HypothesesSet<MinisatSolver>, Lit>(set, i, cstl);
            // Check for literal linkage
            int lit_complement = cstl.x%2 == 0 ? cstl.x+1 : cstl.x-1;
            if (linker.find(lit_complement) == linker.end()) {
                linker[cstl.x] = i;
            } else {
                set.mapLink(i, linker[lit_complement]);
                set.mapLink(linker[lit_complement], i);
            }
        }
    }

}

#endif
