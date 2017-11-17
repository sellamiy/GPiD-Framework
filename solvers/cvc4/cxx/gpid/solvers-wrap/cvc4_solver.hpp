#ifndef GPID_SMT_SOLVER__CVC4_DETAILS_HPP
#define GPID_SMT_SOLVER__CVC4_DETAILS_HPP

#include <gpid/config.hpp>
#include <gpid/solvers-wrap/cvc4_engine.hpp>
#include <gpid/solvers-wrap/cvc4_outputs.hpp>

using namespace snlog;

namespace gpid {

    inline void CVC4Solver::accessLevel(uint32_t level) {
        while (level > c_level) {
            solver.push();
            csty_solver.push();
            c_level++;
        }
        while (level < c_level) {
            solver.pop();
            csty_solver.pop();
            c_level--;
        }
    }

    inline void CVC4Solver::addHypothesis(CVC4Hypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        solver.assertFormula(hypothesis.expr);
        csty_solver.assertFormula(hypothesis.expr);
    }

    inline void CVC4Solver::removeHypotheses(uint32_t level) {
        accessLevel(level - 1);
        accessLevel(level);
    }

    inline void CVC4Solver::printActiveNegation() {
        p_implicate(std::cout, getContextManager(), csty_solver.getAssertions(), true);
    }

    inline void CVC4Solver::storeActive() {
        snlog::l_warn("Not implemented yet - CVC4 active storage");
    }

    inline gpid::SolverTestStatus CVC4Solver::testHypotheses(uint32_t level) {
        accessLevel(level);
        CVC4::Result qres = solver.checkSat();
        if      (qres.isSat() == CVC4::Result::SAT)   return SolverTestStatus::SOLVER_SAT;
        else if (qres.isSat() == CVC4::Result::UNSAT) return SolverTestStatus::SOLVER_UNSAT;
        else                                          return SolverTestStatus::SOLVER_UNKNOWN;
    }

    inline gpid::SolverTestStatus CVC4Solver::checkConsistency(uint32_t level) {
        accessLevel(level);
        CVC4::Result qres = csty_solver.checkSat();
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
