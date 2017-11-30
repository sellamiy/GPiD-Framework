#ifndef GPID_CVC4_SOLVER_INLINED_SPP
#define GPID_CVC4_SOLVER_INLINED_SPP

#include <snlog/snlog.hpp>

namespace gpid {

    class CVC4SolverInternal {
    public:
        CVC4::SmtEngine solver;
        CVC4::SmtEngine csty_solver;
        CVC4ModelWrapper iw_mdl;

        CVC4SolverInternal(CVC4::ExprManager* ctx)
            : solver(ctx), csty_solver(ctx), iw_mdl(solver)
        {
            solver.setOption("incremental", true);
            solver.setOption("produce-models", true);
            solver.setLogic("QF_ALL_SUPPORTED");

            csty_solver.setOption("incremental", true);
            csty_solver.setOption("produce-models", true);
            csty_solver.setLogic("QF_ALL_SUPPORTED");
        }

        inline void push() {
            solver.push();
            csty_solver.push();
        }

        inline void pop() {
            solver.pop();
            csty_solver.pop();
        }

        inline void addHypothesis(CVC4Hypothesis& hypothesis) {
            solver.assertFormula(hypothesis.expr);
            csty_solver.assertFormula(hypothesis.expr);
        }

    };

    inline void CVC4Solver::accessLevel(uint32_t level) {
        while (level > c_level) {
            solvers->push();
            c_level++;
        }
        while (level < c_level) {
            solvers->pop();
            c_level--;
        }
    }

    inline void CVC4Solver::addHypothesis(CVC4Hypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        solvers->addHypothesis(hypothesis);
    }

    inline void CVC4Solver::removeHypotheses(uint32_t level) {
        accessLevel(level - 1);
        accessLevel(level);
    }

    inline void CVC4Solver::printActiveNegation() {
        p_implicate(std::cout, getContextManager(), solvers->csty_solver.getAssertions(), true);
    }

    inline void CVC4Solver::storeActive() {
        snlog::l_warn("Not implemented yet - CVC4 active storage");
    }

    inline CVC4ModelWrapper& CVC4Solver::recoverModel() {
        return solvers->iw_mdl;
    }

    inline gpid::SolverTestStatus CVC4Solver::testHypotheses(uint32_t level) {
        accessLevel(level);
        CVC4::Result qres = solvers->solver.checkSat();
        if      (qres.isSat() == CVC4::Result::SAT)   return SolverTestStatus::SOLVER_SAT;
        else if (qres.isSat() == CVC4::Result::UNSAT) return SolverTestStatus::SOLVER_UNSAT;
        else                                          return SolverTestStatus::SOLVER_UNKNOWN;
    }

    inline gpid::SolverTestStatus CVC4Solver::checkConsistency(uint32_t level) {
        accessLevel(level);
        CVC4::Result qres = solvers->csty_solver.checkSat();
        if      (qres.isSat() == CVC4::Result::SAT)   return SolverTestStatus::SOLVER_SAT;
        else if (qres.isSat() == CVC4::Result::UNSAT) return SolverTestStatus::SOLVER_UNSAT;
        else                                          return SolverTestStatus::SOLVER_UNKNOWN;
    }

    inline bool CVC4Solver::storageSubsumed(CVC4Hypothesis&, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - CVC4 storage subsumption");
        return false;
    }

};

#endif
