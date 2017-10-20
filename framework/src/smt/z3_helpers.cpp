#define Z3_GENERATION_HELPERS
#include <snlog/snlog.hpp>
#include <gpid/util/parsers.hpp>
#include <gpid/util/generators.hpp>
#include <gpid/smt/z3_inputs.hpp>

using namespace snlog;
using namespace z3;

namespace gpid {

    enum z3InputGenerator { Z3IG_NONE, Z3IG_CONST_ALL_EQ };
    static inline z3InputGenerator toZ3InputGenerator(std::string key) {
        if (key == "const-all-eq") return z3InputGenerator::Z3IG_CONST_ALL_EQ;
        else {
            l_error("Unknown z3 abducible generator: " + key);
            return z3InputGenerator::Z3IG_NONE;
        }
    }

    static inline uint32_t z3AbducibleCompt(z3InputGenerator g, Z3Problem& pbl) {
        uint32_t l_gvr;
        switch (g) {
        case Z3IG_NONE: return 0;
        case Z3IG_CONST_ALL_EQ:
            l_gvr = pbl.getDeclarations().getFunDecls().size();
            return l_gvr > 1 ? l_gvr * (l_gvr - 1) : 0;
        default:
            l_internal("Unknown z3 abducible generator: " + std::to_string(g));
            return 0;
        }
    }

    struct z3GeneratorCounter {
        inline uint32_t operator() (std::string gkey, Z3Problem& pbl)
        { return z3AbducibleCompt(toZ3InputGenerator(gkey), pbl); }
    };

    static inline void loadAbducibles
    (std::string filename, z3::context& ctx, Z3Declarations& decls, Z3HypothesesSet& set) {
        alloc_gab<Z3Hypothesis>(set.getSourceSize());
        AbducibleParser parser(filename);
        parser.init();
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            if (!parser.isOk()) {
                l_fatal("Error loading from @file:" + filename);
                break;
            }
            std::string expr = parser.nextAbducible();
            std::string smt_assert = "(assert " + expr + ")";
            z3::expr cstl = ctx.parse_string(smt_assert.c_str(), decls.getSortDecls(), decls.getFunDecls());
            store_gab_hyp<Z3HypothesesSet, z3::expr>(set, i, cstl);
        }
    }

    struct z3Loader {
        inline void operator()
        (std::string filename, z3::context& ctx, Z3Declarations& decls, Z3HypothesesSet& set)
        { loadAbducibles(filename, ctx, decls, set); }
    };

    static inline
    void generateAbducibles_CONST_ALL_EQ(z3::context&, Z3Declarations& decls, Z3HypothesesSet& set) {
        alloc_gab<Z3Hypothesis>(set.getSourceSize());
        uint32_t vCount = decls.getFunDecls().size();
        uint32_t pos = 0;
        for (uint32_t i = 0; i < vCount; i++) {
            for (uint32_t j = i+1; j < vCount; j++) {
                z3::expr cstl_eq = decls.getFunDecls()[i]() == decls.getFunDecls()[j]();
                z3::expr cstl_neq = decls.getFunDecls()[i]() != decls.getFunDecls()[j]();
                store_gab_hyp<Z3HypothesesSet, z3::expr>(set, pos, cstl_eq);
                store_gab_hyp<Z3HypothesesSet, z3::expr>(set, pos+1, cstl_neq);
                set.mapLink(pos, pos+1);
                set.mapLink(pos+1, pos);
                pos += 2;
            }
        }
    }

    static inline
    void generateAbducibles
    (z3InputGenerator g, z3::context& ctx, Z3Declarations& decls, Z3HypothesesSet& set) {
        switch (g) {
        case Z3IG_NONE: break;
        case Z3IG_CONST_ALL_EQ: generateAbducibles_CONST_ALL_EQ(ctx, decls, set);
            break;
        default: l_internal("Unknown minisat abducible generator: " + std::to_string(g));
        }
    }

    struct z3Generator {
        inline void operator()
        (std::string gkey, z3::context& ctx, Z3Declarations& decls, Z3HypothesesSet& set)
        { generateAbducibles(toZ3InputGenerator(gkey), ctx, decls, set); }
    };

    extern uint32_t countAbducibles(AbduciblesOptions& opts, Z3Problem& pbl) {
        return countAbducibles<Z3Problem, z3GeneratorCounter>(opts, pbl);
    }
    extern void generateAbducibles
    (AbduciblesOptions& opts, z3::context& ctx, Z3Declarations& decls, Z3HypothesesSet& hys) {
        generateAbducibles<Z3HypothesesSet, z3::context, Z3Declarations, z3Loader, z3Generator>
            (opts, ctx, decls, hys);
    }

}
