#ifndef GPID_CVC4_GENERATOR_LOADER_SPP
#define GPID_CVC4_GENERATOR_LOADER_SPP

using namespace snlog;
using namespace CVC4;

namespace gpid {

    static inline void handleAbducible
    (int idx, const std::string expr,
     CVC4::ExprManager& em, CVC4Declarations& decls,
     HypothesesSet<CVC4Solver>& set, std::map<int,int>&) {
        CVC4::Options opts4;
        l_warn("Fixme: Abducible Parser - input language as an option"); // TODO
        opts4.setInputLanguage(CVC4::language::input::LANG_SMTLIB_V2);

        CVC4::parser::ParserBuilder pb(&em, "<internal>", opts4);
        CVC4::parser::Parser* p = pb.withStringInput(expr).build();
        p->useDeclarationsFrom(decls.getSymbolTable());
        CVC4::Expr cstl = p->nextExpression();

        store_gab_hyp<HypothesesSet<CVC4Solver>, CVC4::Expr>(set, idx, cstl);
    }

};

#endif
