#ifndef CVC4_API_CONTEXT_FOR_GPID__HPP
#define CVC4_API_CONTEXT_FOR_GPID__HPP

#include <vector>
#include <cvc4/cvc4.h>

namespace gpid {

    class CVC4Declarations {
        CVC4::ExprManager& ctx;
        std::vector<std::string> nameDefs;
        CVC4::SymbolTable* stable;
    public:
        using ContextManagerT = CVC4::ExprManager;
        using ConstraintT = CVC4::Expr;
        CVC4Declarations(CVC4::ExprManager& ctx) : ctx(ctx) {}

        inline CVC4::SymbolTable* getSymbolTable() { return stable; }
        inline std::vector<std::string>::iterator begin() { return nameDefs.begin(); }
        inline std::vector<std::string>::iterator end()   { return nameDefs.end(); }
        inline std::vector<std::string>::const_iterator cbegin() { return nameDefs.cbegin(); }
        inline std::vector<std::string>::const_iterator cend()   { return nameDefs.cend(); }

        void store(CVC4::SymbolTable* table);
        void collect(CVC4::Command* cmd);
    };

    struct CVC4Literal {
        CVC4::Expr expr;
        CVC4Literal(CVC4::Expr e) : expr(e) {}
        CVC4Literal(const CVC4Literal& e) : expr(e.expr) {}

        inline const std::string str() const {
            std::stringstream result; result << expr; return result.str();
        }
    };

    struct CVC4ModelWrapper {
        const CVC4::SmtEngine& engine;
        inline CVC4ModelWrapper(CVC4::SmtEngine& engine) : engine(engine) { }
        inline CVC4ModelWrapper(CVC4ModelWrapper& mdlw) : engine(mdlw.engine) { }
        inline bool implies(CVC4Literal& h) const {
            return engine.getValue(h.expr) == engine.getExprManager()->mkConst(true);
        }
    };

    inline CVC4::Expr asformula(const std::vector<CVC4::Expr>& v,
                                CVC4::ExprManager& ctx, bool negate=false) {
        CVC4::Expr f;
        bool finit = false;
        for (unsigned i = 0; i < v.size(); ++i) {
            if (finit)
                f = ctx.mkExpr(CVC4::Kind::AND, f, v[i]);
            else {
                f = v[i];
                finit = true;
            }
        }        
        if (negate) f = ctx.mkExpr(CVC4::Kind::NOT, f);
        return f;
    }

}

#endif
