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

        inline void addLiteral(CVC4Literal& literal) {
            solver.assertFormula(literal.expr);
            csty_solver.assertFormula(literal.expr);
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

    inline void CVC4Solver::addLiteral(CVC4Literal& literal, uint32_t level) {
        accessLevel(level);
        solvers->addLiteral(literal);
    }

    inline void CVC4Solver::removeLiterals(uint32_t level) {
        accessLevel(level - 1);
        accessLevel(level);
    }

    inline const std::string CVC4Solver::hypothesisAsString() const {
        snlog::l_warn("Not implemented yet - CVC4 Solver literals as string");
        return "";
    }

    inline void CVC4Solver::printHypothesis() {
        snlog::l_warn("Not implemented yet - CVC4 Solver literals printer");
    }

    inline void CVC4Solver::printHypothesisNegation() {
        p_implicate(std::cout, ctx, solvers->csty_solver.getAssertions(), true);
    }

    inline void CVC4Solver::printStoredImplicates() {
        snlog::l_warn("Not implemented yet - CVC4 storage printer");
    }

    inline void CVC4Solver::exportStoredImplicates() {
        snlog::l_warn("Not implemented yet - CVC4 storage exporter");
    }

    inline void CVC4Solver::storeActive() {
        snlog::l_warn("Not implemented yet - CVC4 active storage");
    }

    inline CVC4ModelWrapper& CVC4Solver::recoverModel() {
        return solvers->iw_mdl;
    }

    inline gpid::SolverTestStatus CVC4Solver::testHypothesis(uint32_t level) {
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

    inline bool CVC4Solver::storageSubsumed(CVC4Literal&, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - CVC4 storage subsumption");
        return false;
    }

    inline bool CVC4Solver::isConsequence(CVC4Literal&, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - CVC4 consequence checker");
        return false;
    }

};

#endif
