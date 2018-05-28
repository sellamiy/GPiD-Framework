#ifndef GPID_CVC4_SOLVER_INLINED_SPP
#define GPID_CVC4_SOLVER_INLINED_SPP

#include <snlog/snlog.hpp>

namespace gpid {

    class CVC4SolverInternal {
    public:
        CVC4SolverInternal(CVC4::ExprManager* ctx) : solver(ctx), iw_mdl(solver)
        {
            solver.setOption("incremental", true);
            solver.setOption("produce-models", true);
            solver.setLogic("QF_ALL_SUPPORTED");
        }
        CVC4::SmtEngine solver;
        CVC4ModelWrapper iw_mdl;
    };

    inline void CVC4SolverInterface::push() { _internal->solver.push(); }

    inline void CVC4SolverInterface::pop() { _internal->solver.pop(); }

    inline void CVC4SolverInterface::addLiteral(CVC4Literal& literal, bool negate) {
        if (negate) {
            _internal->solver.assertFormula(ctx.mkExpr(CVC4::kind::NOT, literal.expr));
        } else {
            _internal->solver.assertFormula(literal.expr);
        }
    }

    inline void CVC4SolverInterface::addClause(HypothesisT& h, LiteralMapper<CVC4Literal>& mapper,
                                               bool negate) {
        auto it = h.begin();
        CVC4::Expr cl = mapper.get(*it).expr;
        if (negate) cl = ctx.mkExpr(CVC4::kind::NOT, cl);
        while (++it != h.end()) {
            CVC4::Expr ct = mapper.get(*it).expr;
            if (negate) ct = ctx.mkExpr(CVC4::kind::NOT, ct);
            cl = ctx.mkExpr(CVC4::kind::OR, cl, ct);
        }
        _internal->solver.assertFormula(cl);
    }

    inline CVC4ModelWrapper& CVC4SolverInterface::getModel() {
        return _internal->iw_mdl;
    }

    inline void CVC4SolverInterface::printAssertions(bool negated) {
        p_implicate(std::cout, ctx, _internal->solver.getAssertions(), negated);
    }

    inline const std::string CVC4SolverInterface::getPrintableAssertions(bool) {
        snlog::l_warn("Not Implemented Yet: CVC4 Engine Printable Ssertions"); return "";
    }

    inline gpid::SolverTestStatus CVC4SolverInterface::check() {
        CVC4::Result qres = _internal->solver.checkSat();
        if      (qres.isSat() == CVC4::Result::SAT)   return SolverTestStatus::SAT;
        else if (qres.isSat() == CVC4::Result::UNSAT) return SolverTestStatus::UNSAT;
        else                                          return SolverTestStatus::UNKNOWN;
    }

}

#endif
