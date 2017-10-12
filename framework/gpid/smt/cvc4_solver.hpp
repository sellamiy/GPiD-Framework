#ifndef GPID_SMT_SOLVER__CVC4_DETAILS_HPP
#define GPID_SMT_SOLVER__CVC4_DETAILS_HPP

#include <gpid/config.hpp>
#include <gpid/smt/cvc4_engine.hpp>

using namespace snlog;

namespace gpid {

    inline void CVC4Solver::accessLevel(uint32_t level) {
        while (level > c_level) {
            solver.push();
            c_level++;
        }
        while (level < c_level) {
            solver.pop();
            c_level--;
        }
    }

    inline void CVC4Solver::addHypothesis(CVC4Hypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        solver.assertFormula(hypothesis.expr);
    }

    inline void CVC4Solver::printActiveNegation() {
        snlog::l_warn("Not implemented yet - CVC4 active negation printer");
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

    inline bool CVC4Solver::currentlySubsumed(CVC4Hypothesis& additional, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - CVC4 storage subsumption");
        return false;
    }

};

#endif
