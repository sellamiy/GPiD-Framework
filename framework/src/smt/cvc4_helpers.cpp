#define CVC4_GENERATION_HELPERS
#include <snlog/snlog.hpp>
#include <gpid/util/parsers.hpp>
#include <gpid/util/generators.hpp>
#include <gpid/smt/cvc4_inputs.hpp>

using namespace snlog;
using namespace CVC4;

static const std::string c4helpers_gab_tag = "CVC4Hypotheses";
/*
extern void gpid::initRawSet(ExprManager& em, CVC4HypothesesSet& set) {
    GAB_Status res;
    res = requestContinuousArray(c4helpers_gab_tag, set.getSourceSize(), sizeof(CVC4Hypothesis));
    if (res != GAB_Status::SUCCESS) l_error("Memory request for minisat hypotheses wrappers failed!");
    for (uint32_t i = 0; i < set.getSourceSize(); i++) {
        Expr cstl = em.mkConst(false);
        l_warn("Fixme: add correct abducible instanciation for cvc4 expression instances"); // TODO
        CVC4Hypothesis *mloc;
        res = accessContinuousPointer(c4helpers_gab_tag, i, (void**)&mloc);
        if (res != GAB_Status::SUCCESS) l_error("Memory access for minisat hypothesis wrapper failed!");
        new (mloc) CVC4Hypothesis(cstl);
        set.mapHypothesis(i, mloc);
        // set.mapLink(i, i%2 == 0 ? i+1 : i-1); // TODO Linkage
        l_warn("Fixme: possibly, add abducible linkage for cvc4 expression instances"); // TODO
    }
}
*/
namespace gpid {

    enum c4InputGenerator { C4IG_NONE };
    static inline c4InputGenerator toC4InputGenerator(std::string key) {
        /*
        if (key == "machin") return mInputGenerator::C4IG_MACHIN;
        else {
        */
        l_error("Unknown cvc4 abducible generator: " + key);
        l_info("Currently, there are no cvc4 abducible generator available");
        return c4InputGenerator::C4IG_NONE;
        /*}*/
    }

    static inline uint32_t c4AbducibleCompt(c4InputGenerator g, CVC4Problem& pbl) {
        switch (g) {
        case C4IG_NONE: return 0;
        default:
            l_internal("Unknown cvc4 abducible generator: " + std::to_string(g));
            return 0;
        }
    }

    struct c4GeneratorCounter {
        inline uint32_t operator() (std::string gkey, CVC4Problem& pbl)
        { return c4AbducibleCompt(toC4InputGenerator(gkey), pbl); }
    };

    static inline void loadAbducibles(std::string filename, CVC4::ExprManager& em, CVC4HypothesesSet& set) {
        alloc_gab<CVC4Hypothesis>(set.getSourceSize());
        AbducibleParser parser(filename);
        parser.init();
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            if (!parser.isOk()) {
                l_fatal("Error loading from @file:" + filename);
                break;
            }
            std::string expr = parser.nextAbducible();

            CVC4::Options opts4;
            l_warn("Fixme: Abducible Parser - input language as an option"); // TODO
            opts4.setInputLanguage(CVC4::language::input::LANG_SMTLIB_V2);

            CVC4::parser::ParserBuilder pb(&em, "<internal>", opts4);
            CVC4::parser::Parser* p = pb.withStringInput(expr).build();
            l_warn("Fixme: This is Broken, we need context preservation");
            CVC4::Expr cstl = p->nextExpression(); // TODO: BROKEN

            store_gab_hyp<CVC4HypothesesSet, CVC4::Expr>(set, i, cstl);
        }
    }

    struct c4Loader {
        inline void operator() (std::string filename, CVC4::ExprManager& em, CVC4HypothesesSet& set)
        { loadAbducibles(filename, em, set); }
    };

    static inline
    void generateAbducibles(c4InputGenerator g, CVC4::ExprManager& em, CVC4HypothesesSet& set) {
        switch (g) {
        case C4IG_NONE: break;
            break;
        default: l_internal("Unknown minisat abducible generator: " + std::to_string(g));
        }
    }

    struct c4Generator {
        inline void operator() (std::string gkey, CVC4::ExprManager& em, CVC4HypothesesSet& set)
        { generateAbducibles(toC4InputGenerator(gkey), em, set); }
    };

    extern uint32_t countAbducibles(AbduciblesOptions& opts, CVC4Problem& pbl) {
        return countAbducibles<CVC4Problem, c4GeneratorCounter>(opts, pbl);
    }
    extern void generateAbducibles(AbduciblesOptions& opts, CVC4::ExprManager& em, CVC4HypothesesSet& hys) {
        generateAbducibles<CVC4HypothesesSet, CVC4::ExprManager, c4Loader, c4Generator>(opts, em, hys);
    }

}
