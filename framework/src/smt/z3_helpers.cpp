#define Z3_GENERATION_HELPERS
#include <snlog/snlog.hpp>
#include <gpid/util/parsers.hpp>
#include <gpid/util/generators.hpp>
#include <gpid/smt/z3_inputs.hpp>

using namespace snlog;
using namespace z3;

static const std::string z3helpers_gab_tag = "Z3Hypotheses";
/*
extern void gpid::initRawSet(context& ctx, Z3HypothesesSet& set) {
    GAB_Status res;
    res = requestContinuousArray(z3helpers_gab_tag, set.getSourceSize(), sizeof(Z3Hypothesis));
    t_error(res != GAB_Status::SUCCESS, "Memory request for minisat hypotheses wrappers failed!");
    for (uint32_t i = 0; i < set.getSourceSize(); i++) {
        expr cstl = ctx.bool_val(false);
        l_warn("Fixme: add correct abducible instanciation for z3 expression instances"); // TODO
        Z3Hypothesis *mloc;
        res = accessContinuousPointer(z3helpers_gab_tag, i, (void**)&mloc);
        t_error(res != GAB_Status::SUCCESS, "Memory access for minisat hypothesis wrapper failed!");
        new (mloc) Z3Hypothesis(cstl);
        set.mapHypothesis(i, mloc);
        // set.mapLink(i, i%2 == 0 ? i+1 : i-1); // TODO Linkage
        l_warn("Fixme: possibly, add abducible linkage for z3 expression instances"); // TODO
    }
}
*/
namespace gpid {

    enum z3InputGenerator { Z3IG_NONE };
    static inline z3InputGenerator toZ3InputGenerator(std::string key) {
        /*
        if (key == "machin") return mInputGenerator::Z3IG_MACHIN;
        else {
        */
        l_error("Unknown z3 abducible generator: " + key);
        l_info("Currently, there are no z3 abducible generator available");
        return z3InputGenerator::Z3IG_NONE;
        /*}*/
    }

    static inline uint32_t z3AbducibleCompt(z3InputGenerator g, Z3Problem& pbl) {
        switch (g) {
        case Z3IG_NONE: return 0;
        default:
            l_internal("Unknown z3 abducible generator: " + std::to_string(g));
            return 0;
        }
    }

    struct z3GeneratorCounter {
        inline uint32_t operator() (std::string gkey, Z3Problem& pbl)
        { return z3AbducibleCompt(toZ3InputGenerator(gkey), pbl); }
    };

    static inline void loadAbducibles(std::string filename, z3::context& ctx, Z3HypothesesSet& set) {
        // TODO : Update
        l_warn("Not implemented Yet : Z3 Abducible loader");
    }

    struct z3Loader {
        inline void operator() (std::string filename, z3::context& ctx, Z3HypothesesSet& set)
        { loadAbducibles(filename, ctx, set); }
    };

    static inline
    void generateAbducibles(z3InputGenerator g, z3::context& ctx, Z3HypothesesSet& set) {
        switch (g) {
        case Z3IG_NONE: break;
            break;
        default: l_internal("Unknown minisat abducible generator: " + std::to_string(g));
        }
    }

    struct z3Generator {
        inline void operator() (std::string gkey, z3::context& ctx, Z3HypothesesSet& set)
        { generateAbducibles(toZ3InputGenerator(gkey), ctx, set); }
    };

    extern uint32_t countAbducibles(AbduciblesOptions& opts, Z3Problem& pbl) {
        return countAbducibles<Z3Problem, z3GeneratorCounter>(opts, pbl);
    }
    extern void generateAbducibles(AbduciblesOptions& opts, z3::context& ctx, Z3HypothesesSet& hys) {
        generateAbducibles<Z3HypothesesSet, z3::context, z3Loader, z3Generator>(opts, ctx, hys);
    }

}
