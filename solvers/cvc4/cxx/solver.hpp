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

    inline void CVC4SolverInterface::addLiteral(CVC4Literal& literal) {
        _internal->solver.assertFormula(literal.expr);
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
        if      (qres.isSat() == CVC4::Result::SAT)   return SolverTestStatus::SOLVER_SAT;
        else if (qres.isSat() == CVC4::Result::UNSAT) return SolverTestStatus::SOLVER_UNSAT;
        else                                          return SolverTestStatus::SOLVER_UNKNOWN;
    }

}

#endif
