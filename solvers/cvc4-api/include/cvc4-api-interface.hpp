#ifndef CVC4_API_INTERFACE_FOR_GPID__HPP
#define CVC4_API_INTERFACE_FOR_GPID__HPP

#include "cvc4-api-context.hpp"
#include "cvc4-api-loaders.hpp"
#include "cvc4-api-printers.hpp"
#include "cvc4-api-abdgen.hpp"

namespace gpid {

    class CVC4InterfaceAPI {
        CVC4::ExprManager& ctx;
        CVC4::SmtEngine solver;
        CVC4ModelWrapper iw_mdl;
    public:
        using ContextManagerT = CVC4::ExprManager;
        using ConstraintT = CVC4::Expr;
        using LiteralT = CVC4Literal;
        using ModelT = CVC4ModelWrapper;
        using ProblemLoaderT = CVC4ProblemLoader;

        void push();
        void pop();
        void addLiteral(LiteralT& lit, bool negate=false);
        void addConstraint(ConstraintT cons);
        SolverTestStatus check();
        ModelT& getModel();

        void printAssertions(bool negated);
        const std::string getPrintableAssertions(bool negated);

        template<typename ConjunctionIteratorGetter> static std::ostream& write
        (std::ostream& os, ContextManagerT& ctx, ConjunctionIteratorGetter& h,
         ObjectMapper<CVC4Literal>& mapper, bool negate=false);

        template<typename ClauseIteratorGetter> void addClause
        (ClauseIteratorGetter& h, ObjectMapper<LiteralT>& mapper, bool negate=false);
        void clearUnsafeClauses();

        CVC4InterfaceAPI(CVC4::ExprManager& ctx);
        CVC4::ExprManager& getContextManager();
    };

    inline CVC4::ExprManager& CVC4InterfaceAPI::getContextManager() { return ctx; }

    inline void CVC4InterfaceAPI::push() { solver.push(); }

    inline void CVC4InterfaceAPI::pop() { solver.pop(); }

    inline void CVC4InterfaceAPI::addLiteral(CVC4Literal& literal, bool negate) {
        if (negate) {
            solver.assertFormula(ctx.mkExpr(CVC4::kind::NOT, literal.expr));
        } else {
            solver.assertFormula(literal.expr);
        }
    }

    inline void CVC4InterfaceAPI::addConstraint(ConstraintT cons) {
        solver.assertFormula(cons);
    }

    template<typename ClauseIteratorGetter>
    inline void CVC4InterfaceAPI::addClause
    (ClauseIteratorGetter& h, ObjectMapper<CVC4Literal>& mapper, bool negate) {
        auto it = h.begin();
        CVC4::Expr cl = mapper.get(*it).expr;
        if (negate) cl = ctx.mkExpr(CVC4::kind::NOT, cl);
        while (++it != h.end()) {
            CVC4::Expr ct = mapper.get(*it).expr;
            if (negate) ct = ctx.mkExpr(CVC4::kind::NOT, ct);
            cl = ctx.mkExpr(CVC4::kind::OR, cl, ct);
        }
        solver.assertFormula(cl);
    }

    template<typename ConjunctionIteratorGetter>
    inline std::ostream& CVC4InterfaceAPI::write
    (std::ostream& os, ContextManagerT& ctx, ConjunctionIteratorGetter& h,
     ObjectMapper<CVC4Literal>& mapper, bool negate) {
        auto it = h.begin();
        CVC4::Expr cl = mapper.get(*it).expr;
        while (++it != h.end()) {
            CVC4::Expr ct = mapper.get(*it).expr;
            cl = ctx.mkExpr(CVC4::kind::AND, cl, ct);
        }
        if (negate) cl = ctx.mkExpr(CVC4::kind::NOT, cl);
        return os << cl;
    }

    inline CVC4ModelWrapper& CVC4InterfaceAPI::getModel() {
        return iw_mdl;
    }

    inline void CVC4InterfaceAPI::clearUnsafeClauses() { }

    inline void CVC4InterfaceAPI::printAssertions(bool negated) {
        p_implicate(std::cout, ctx, solver.getAssertions(), negated);
    }

    inline const std::string CVC4InterfaceAPI::getPrintableAssertions(bool) {
        std::stringstream result;
        result << asformula(solver.getAssertions(), ctx);
        return result.str();
    }

    inline gpid::SolverTestStatus CVC4InterfaceAPI::check() {
        CVC4::Result qres = solver.checkSat();
        if      (qres.isSat() == CVC4::Result::SAT)   return SolverTestStatus::SAT;
        else if (qres.isSat() == CVC4::Result::UNSAT) return SolverTestStatus::UNSAT;
        else                                          return SolverTestStatus::UNKNOWN;
    }

}

#endif
