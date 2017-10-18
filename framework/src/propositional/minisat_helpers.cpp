#define MINISAT_GENERATION_HELPERS
#include <snlog/snlog.hpp>
#include <gpid/util/parsers.hpp>
#include <gpid/util/generators.hpp>
#include <gpid/propositional/minisat_inputs.hpp>

using namespace snlog;
using namespace Minisat;

namespace gpid {

    struct mContext {};

    enum mInputGenerator { MIG_NONE, MIG_ALL };
    static inline mInputGenerator toMInputGenerator(std::string key) {
        if (key == "all") return mInputGenerator::MIG_ALL;
        else {
            l_error("Unknown minisat abducible generator: " + key);
            return mInputGenerator::MIG_NONE;
        }
    }

    static inline uint32_t mAbducibleCompt(mInputGenerator g, MinisatProblem& pbl) {
        switch (g) {
        case MIG_NONE: return 0;
        case MIG_ALL: return 2*pbl.getVarCpt();
        default:
            l_internal("Unknown minisat abducible generator: " + std::to_string(g));
            return 0;
        }
    }

    struct mGeneratorCounter {
        inline uint32_t operator() (std::string gkey, MinisatProblem& pbl)
        { return mAbducibleCompt(toMInputGenerator(gkey), pbl); }
    };

    struct mDeclsInfo {
        const int nVars;
        inline mDeclsInfo(int n) : nVars(n) {}
    };

    static inline void loadAbducibles(std::string filename, MinisatHypothesesSet& set) {
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
            store_gab_hyp<MinisatHypothesesSet, Lit>(set, i, cstl);
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

    struct mLoader {
        inline void operator() (std::string filename, mContext&, mDeclsInfo&, MinisatHypothesesSet& set)
        { loadAbducibles(filename, set); }
    };

    static inline void generateAbducibles_ALL(MinisatHypothesesSet& set) {
        alloc_gab<MinisatHypothesis>(set.getSourceSize());
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            Lit cstl;
            cstl.x = i;
            store_gab_hyp<MinisatHypothesesSet, Lit>(set, i, cstl);
            set.mapLink(i, i%2 == 0 ? i+1 : i-1);
        }
    }

    static inline void generateAbducibles(mInputGenerator g, MinisatHypothesesSet& set) {
        switch (g) {
        case MIG_NONE: break;
        case MIG_ALL: generateAbducibles_ALL(set);
            break;
        default: l_internal("Unknown minisat abducible generator: " + std::to_string(g));
        }
    }

    struct mGenerator {
        inline void operator() (std::string gkey, mContext&, mDeclsInfo&, MinisatHypothesesSet& set)
        { generateAbducibles(toMInputGenerator(gkey), set); }
    };

    extern uint32_t countAbducibles(AbduciblesOptions& opts, MinisatProblem& pbl) {
        return countAbducibles<MinisatProblem, mGeneratorCounter>(opts, pbl);
    }
    extern void generateAbducibles(AbduciblesOptions& opts, MinisatHypothesesSet& hys, int nVars) {
        mContext dummy;
        mDeclsInfo decls(nVars);
        generateAbducibles<MinisatHypothesesSet, mContext, mDeclsInfo, mLoader, mGenerator>
            (opts, dummy, decls, hys);
    }

}
