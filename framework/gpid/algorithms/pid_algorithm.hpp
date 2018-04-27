/**
 * \file gpid/algorithms/pid_algorithm.hpp
 * \brief PiD decomposition algorithm implementation.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__ALGORITHMS__PID_ALGORITHM_HPP
#define GPID_FRAMEWORK__ALGORITHMS__PID_ALGORITHM_HPP

#include <gpid/core/engine.hpp>

using namespace snlog;

/* ========== PID Helpers =========== */

template<class SolverT>
void gpid::DecompositionEngine<SolverT>::selectNextPID() {
    // Recovering next possible hypothesis
    bool has_next = hengine.nextHypothesis(level);
    if (has_next) {
        hengine.backtrack(level);
        hengine.selectCurrentHypothesis();
        pushStackLevel();
    } else {
        // Actually no more hypotheses
        popStackLevel();
    }
}

/* ========== PID Algorithm ========== */

template<class SolverT>
void gpid::DecompositionEngine<SolverT>::generatePID() {
    resetEngine();

    while (level > 0 && !des_iflags.systemInterrupted()) {
        if (sdir == IStackDirection::STACK_POP) {

            selectNextPID();

        } else {
            node_counter++;

            SolverTestStatus status = hengine.testHypotheses(level);

            if (status == SolverTestStatus::SOLVER_SAT) {
                if (options.use_models) {
                    hengine.modelCleanUp(level);
                }
                selectNextPID();
            } else if (status == SolverTestStatus::SOLVER_UNSAT) {
                // We have found an implicate
                activeIsImplicate();
                popStackLevel();
            } else {
                throw UndecidableProblemError("Solver could not decide query");
            }

        }

    }

    if (options.print_storage) {
        hengine.printStorage();
    }
}

#endif
