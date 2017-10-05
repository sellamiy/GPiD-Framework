#ifndef GPID_PID_ALGORITHMS_HPP
#define GPID_PID_ALGORITHMS_HPP

#include <snlog/snlog.hpp>
#include <gpid/core/engine.hpp>

using namespace snlog;

/* ========== PID Helpers =========== */

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::selectNextPID() {
    while (!available_h.isEmpty(level)) {
        // Recovering next possible hypothesis
        HypothesisT& sel = available_h.nextHypothesis(level);
        /* TODO: Maybe, skip these just once after the test to prevent model storage */
        if (solver.isModelSkippable(sel, level)) continue;
        // Actual possible hypothesis
        solver.addHypothesis(sel, level);
        pushStackLevel();
        return;
    }
    // Actually no more hypotheses
    popStackLevel();
}

/* ========== PID Algorithm ========== */

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::generatePID() {
    resetEngine();

    while (level > 0) {

        if (sdir == IStackDirection::STACK_POP) {

            selectNextPID();

        } else {

            SolverTestStatus status = solver.testHypotheses(level);

            if (status == SolverTestStatus::SOLVER_SAT) {
                selectNextPID();
            } else if (status == SolverTestStatus::SOLVER_UNSAT) {
                // We have found an implicate
                activeIsImplicate();
                popStackLevel();
            } else {
                // Solver UNKNOWN :: ERROR
                l_fatal("Solver could not decide query!");
            }

        }

    }

}

#endif
