#ifndef GPID_SMT_SOLVER__Z3_DETAILS_HPP
#define GPID_SMT_SOLVER__Z3_DETAILS_HPP

#include <gpid/config.hpp>
#include <gpid/smt/z3_engine.hpp>
#include <gpid/smt/z3_outputs.hpp>

using namespace snlog;

namespace gpid {

    inline void Z3Solver::accessLevel(uint32_t level) {
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

    inline void Z3Solver::addHypothesis(Z3Hypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        solver.add(hypothesis.expr);
        csty_solver.add(hypothesis.expr);
    }

    inline void Z3Solver::removeHypotheses(uint32_t level) {
        accessLevel(level - 1);
        accessLevel(level);
    }

    inline void Z3Solver::printActiveNegation() {
        p_implicate(std::cout, ctx, csty_solver.assertions(), true);
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

    inline gpid::SolverTestStatus Z3Solver::checkConsistency(uint32_t level) {
        accessLevel(level);
        z3::check_result qres = csty_solver.check();
        switch (qres) {
        case z3::sat:   return SolverTestStatus::SOLVER_SAT;
        case z3::unsat: return SolverTestStatus::SOLVER_UNSAT;
        default:        return SolverTestStatus::SOLVER_UNKNOWN;
        }
    }

    inline bool Z3Solver::storageSubsumed(Z3Hypothesis&, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - Z3 storage subsumption");
        return false;
    }

};

#endif
