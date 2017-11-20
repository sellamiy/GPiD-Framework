#define CVC4_GENERATION_HELPERS
#include <snlog/snlog.hpp>
#include <gpid/util/parsers.hpp>
#include <gpid/util/generators.hpp>
#include <gpid/solvers-wrap/cvc4_inputs.hpp>

using namespace snlog;
using namespace CVC4;

namespace gpid {

    enum c4InputGenerator { C4IG_NONE, C4IG_ALL_EQ };
    static std::map<std::string, c4InputGenerator> c4InputGeneratorTable =
        { { "all-eq", C4IG_ALL_EQ } };
    static inline c4InputGenerator toC4InputGenerator(std::string key) {
        if (c4InputGeneratorTable[key] == c4InputGenerator::C4IG_NONE) {
            l_error("Unknown cvc4 abducible generator: " + key);
            for (std::pair<std::string, c4InputGenerator> akey : c4InputGeneratorTable) {
                if (akey.second != C4IG_NONE)
                    l_info("   -- available: " + akey.first);
            }
        }
        return c4InputGeneratorTable[key];
    }

    static inline
    void abduciblesUtils_ALL_EQ(CVC4::ExprManager& ctx,
                                CVC4Declarations& decls,
                                std::vector<CVC4::Expr>& knownVars) {
        /*
         * Delegate symbol accesses to a dummy parser as direct accesses
         * to the symbolTable seem to raise segmentation faults.
         */
        CVC4::Options opts4;
        opts4.setInputLanguage(CVC4::language::input::LANG_SMTLIB_V2);
        CVC4::parser::ParserBuilder pb(&ctx, "<internal>", opts4);
        CVC4::parser::Parser* p = pb.withStringInput("").build();
        p->useDeclarationsFrom(decls.getSymbolTable());

        /* Building a type table for abducible generation */
        std::map<CVC4::Type, std::list<Expr>> typeTable;
        for (const std::string decl : decls) {
            CVC4::Expr fun = p->getFunction(decl);
            if (fun.getType().isFunction()) {
                snlog::l_warn("Function are currently not handles by this CVC4 abducible generator");
                // TODO : Handle functions
                // snlog::l_info(fun.getType());
                // snlog::l_info(fun.getType().getBaseType());
            } else {
                knownVars.push_back(fun);
                typeTable[fun.getType()].push_back(fun);
            }
        }
    }

    static inline uint32_t countAbducibles_ALL_EQ(CVC4::ExprManager& ctx, CVC4Declarations& decls) {
        std::vector<CVC4::Expr> knownVars;
        abduciblesUtils_ALL_EQ(ctx, decls, knownVars);
        return knownVars.size() > 1 ? knownVars.size() * (knownVars.size() - 1) : 0;
    }

    static inline uint32_t c4AbducibleCompt(c4InputGenerator g, CVC4Problem& pbl) {
        switch (g) {
        case C4IG_NONE: return 0;
        case C4IG_ALL_EQ: return countAbducibles_ALL_EQ(pbl.getExprManager(), pbl.getDeclarations());
        default:
            l_internal("Unknown cvc4 abducible generator: " + std::to_string(g));
            return 0;
        }
    }

    struct c4GeneratorCounter {
        inline uint32_t operator() (std::string gkey, CVC4Problem& pbl)
        { return c4AbducibleCompt(toC4InputGenerator(gkey), pbl); }
    };

    static inline void loadAbducibles
    (std::string filename, CVC4::ExprManager& em, CVC4Declarations& decls, CVC4HypothesesSet& set) {
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
            p->useDeclarationsFrom(decls.getSymbolTable());
            CVC4::Expr cstl = p->nextExpression();

            store_gab_hyp<CVC4HypothesesSet, CVC4::Expr>(set, i, cstl);
        }
    }

    struct c4Loader {
        inline void operator()
        (std::string filename, CVC4::ExprManager& em, CVC4Declarations& decls, CVC4HypothesesSet& set)
        { loadAbducibles(filename, em, decls, set); }
    };

    static inline
    void generateAbducibles_ALL_EQ(CVC4::ExprManager& ctx,
                                   CVC4Declarations& decls, CVC4HypothesesSet& set) {
        std::vector<CVC4::Expr> knownVars;
        abduciblesUtils_ALL_EQ(ctx, decls, knownVars);

        /* Building abducibles */
        uint32_t pos = 0;
        alloc_gab<CVC4HypothesesSet>(set.getSourceSize());
        for (uint32_t i = 0; i < knownVars.size(); i++) {
            for (uint32_t j = i + 1; j < knownVars.size(); j++) {
                CVC4::Expr eq_expr  = ctx.mkExpr(kind::EQUAL, knownVars[i], knownVars[j]);
                CVC4::Expr neq_expr = ctx.mkExpr(kind::DISTINCT, knownVars[i], knownVars[j]);
                store_gab_hyp<CVC4HypothesesSet, CVC4::Expr>(set, pos, eq_expr);
                store_gab_hyp<CVC4HypothesesSet, CVC4::Expr>(set, pos+1, neq_expr);
                set.mapLink(pos, pos+1);
                set.mapLink(pos+1, pos);
                pos += 2;
            }
        }
    }

    static inline
    void generateAbducibles
    (c4InputGenerator g, CVC4::ExprManager& ctx, CVC4Declarations& decls, CVC4HypothesesSet& set) {
        switch (g) {
        case C4IG_NONE: break;
        case C4IG_ALL_EQ: generateAbducibles_ALL_EQ(ctx, decls, set);
            break;
        default: l_internal("Unknown minisat abducible generator: " + std::to_string(g));
        }
    }

    struct c4Generator {
        inline void operator()
        (std::string gkey, CVC4::ExprManager& em, CVC4Declarations& decls, CVC4HypothesesSet& set)
        { generateAbducibles(toC4InputGenerator(gkey), em, decls, set); }
    };

    extern uint32_t countAbducibles(AbduciblesOptions& opts, CVC4Problem& pbl) {
        return countAbducibles<CVC4Problem, c4GeneratorCounter>(opts, pbl);
    }
    extern void generateAbducibles
    (AbduciblesOptions& opts, CVC4::ExprManager& em, CVC4Declarations& decls, CVC4HypothesesSet& hys) {
        generateAbducibles<CVC4HypothesesSet, CVC4::ExprManager, CVC4Declarations, c4Loader, c4Generator>
            (opts, em, decls, hys);
    }

}
