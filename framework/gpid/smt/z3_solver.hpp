#ifndef GPID_SMT_SOLVER__Z3_DETAILS_HPP
#define GPID_SMT_SOLVER__Z3_DETAILS_HPP

#include <gpid/config.hpp>
#include <gpid/smt/z3_engine.hpp>

using namespace snlog;

namespace gpid {

    inline void Z3Solver::accessLevel(uint32_t level) {
        while (level > c_level) {
            solver.push();
            c_level++;
        }
        while (level < c_level) {
            solver.pop();
            c_level--;
        }
    }

    inline void Z3Solver::addHypothesis(Z3Hypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        solver.add(hypothesis.expr);
    }

    inline void Z3Solver::printActiveNegation() {
        snlog::l_warn("Not implemented yet - Z3 active negation printer");
    }

    inline void Z3Solver::storeActive() {
        snlog::l_warn("Not implemented yet - Z3 active storage");
    }

    inline gpid::SolverTestStatus Z3Solver::testHypotheses(uint32_t level) {
        accessLevel(level);
        z3::check_result qres = solver.check();
        switch (qres) {
        case z3::sat:   return SolverTestStatus::SOLVER_SAT;
        case z3::unsat: return SolverTestStatus::SOLVER_UNSAT;
        default:        return SolverTestStatus::SOLVER_UNKNOWN;
        }
    }

    inline bool Z3Solver::currentlySubsumed(Z3Hypothesis& additional, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - Z3 storage subsumption");
        return false;
    }

};

#endif
