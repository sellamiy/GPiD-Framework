#ifndef GPID_CVC4_GENERATOR_ALL_EQ_SPP
#define GPID_CVC4_GENERATOR_ALL_EQ_SPP

using namespace snlog;
using namespace CVC4;

namespace gpid {

    static inline
    void abduciblesUtils_allEq(CVC4::ExprManager& ctx,
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

    static inline uint32_t countAbducibles_allEq(CVC4::ExprManager& ctx, CVC4Declarations& decls) {
        std::vector<CVC4::Expr> knownVars;
        abduciblesUtils_allEq(ctx, decls, knownVars);
        return knownVars.size() > 1 ? knownVars.size() * (knownVars.size() - 1) : 0;
    }

    static inline
    void generateAbducibles_allEq(CVC4::ExprManager& ctx,
                                   CVC4Declarations& decls, LiteralsEngine<CVC4Solver>& set) {
        std::vector<CVC4::Expr> knownVars;
        abduciblesUtils_allEq(ctx, decls, knownVars);

        /* Building abducibles */
        uint32_t pos = 0;
        alloc_gab<LiteralsEngine<CVC4Solver>>(set.getSourceSize());
        for (uint32_t i = 0; i < knownVars.size(); i++) {
            for (uint32_t j = i + 1; j < knownVars.size(); j++) {
                CVC4::Expr eq_expr  = ctx.mkExpr(kind::EQUAL, knownVars[i], knownVars[j]);
                CVC4::Expr neq_expr = ctx.mkExpr(kind::DISTINCT, knownVars[i], knownVars[j]);
                store_gab_hyp<LiteralsEngine<CVC4Solver>, CVC4::Expr>(set, pos, eq_expr);
                store_gab_hyp<LiteralsEngine<CVC4Solver>, CVC4::Expr>(set, pos+1, neq_expr);
                set.mapLink(pos, pos+1);
                set.mapLink(pos+1, pos);
                pos += 2;
            }
        }
    }

};

#endif
