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
    // Recovering next possible literal
    bool has_next = lengine.nextLiteral(level);
    if (has_next) {
        lengine.backtrack(level);
        lengine.selectCurrentLiteral();
        pushStackLevel();
    } else {
        // Actually no more literals
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

            SolverTestStatus status = lengine.testHypothesis(level);

            if (status == SolverTestStatus::SAT) {
                if (options.use_models) {
                    lengine.modelCleanUp(level);
                }
                selectNextPID();
            } else if (status == SolverTestStatus::UNSAT) {
                // We have found an implicate
                activeIsImplicate();
                popStackLevel();
            } else {
                throw UndecidableProblemError("Solver could not decide query");
            }

        }

    }

    if (options.print_storage)  lengine.printStorage();
    if (options.export_storage) lengine.exportStorage();
}

#endif
