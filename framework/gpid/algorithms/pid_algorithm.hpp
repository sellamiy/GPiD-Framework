#ifndef GPID_PID_ALGORITHMS_HPP
#define GPID_PID_ALGORITHMS_HPP

#include <snlog/snlog.hpp>
#include <gpid/core/engine.hpp>

using namespace snlog;

/* ========== PID Helpers =========== */

template<class HypothesisT, class ProblemT, class SolverT, class ModelT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT, ModelT>::selectNextPID() {
    if (!available_h.isEmpty(level)) {
        // Recovering next possible hypothesis
        HypothesisT& sel = available_h.nextHypothesis(level);
        // Actual possible hypothesis
        solver.addHypothesis(sel, level);
        pushStackLevel();
    } else {
        // Actually no more hypotheses
        popStackLevel();
    }
}

/* ========== PID Algorithm ========== */

template<class HypothesisT, class ProblemT, class SolverT, class ModelT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT, ModelT>::generatePID() {
    resetEngine();

    while (level > 0) {

        if (sdir == IStackDirection::STACK_POP) {

            selectNextPID();

        } else {

            SolverTestStatus status = solver.testHypotheses(level);

            if (status == SolverTestStatus::SOLVER_SAT) {
                available_h.modelCleanUp(solver.recoverModel(), level);
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
