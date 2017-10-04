#ifndef GPID_GENERATION_ALGORITHMS_HPP
#define GPID_GENERATION_ALGORITHMS_HPP

#include <snlog/snlog.hpp>
#include <gpid/core/engine.hpp>

using namespace snlog;

/* ========== BPD Algorithm ========== */

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::generateBPD() {
    resetEngine();

    while (level > 0) {

        if (sdir == IStackDirection::STACK_POP) {

            if (!available_h.isEmpty(level)) {
                // Trying next hypothesis
                HypothesisT& sel = available_h.nextHypothesis(level);
                solver.addHypothesis(sel, level);
                pushStackLevel();
            } else {
                // No more hypotheses here
                popStackLevel();
            }

        } else {

            SolverTestStatus status = solver.testHypotheses(level);
            if (status == SolverTestStatus::SOLVER_SAT) {
                if (!available_h.isEmpty(level)) {
                    // Trying next hypothesis
                    HypothesisT& sel = available_h.nextHypothesis(level);
                    solver.addHypothesis(sel, level);
                    pushStackLevel();
                } else {
                    // No more hypotheses here
                    popStackLevel();
                }
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
