#ifndef GPID_CVC4_GENERATOR_LOADER_SPP
#define GPID_CVC4_GENERATOR_LOADER_SPP

using namespace snlog;
using namespace CVC4;

namespace gpid {

    static inline void loadAbducibles
    (std::string filename, CVC4::ExprManager& em, CVC4Declarations& decls, HypothesesSet<CVC4Solver>& set) {
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

            store_gab_hyp<HypothesesSet<CVC4Solver>, CVC4::Expr>(set, i, cstl);
        }
    }

};

#endif
