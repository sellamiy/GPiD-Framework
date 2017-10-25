#ifndef GPID_PID_ALGORITHMS_HPP
#define GPID_PID_ALGORITHMS_HPP

#include <snlog/snlog.hpp>
#include <gpid/core/engine.hpp>

using namespace snlog;

/* ========== PID Helpers =========== */

template<class SolverT>
extern void gpid::DecompositionEngine<SolverT>::selectNextPID() {
    // Recovering next possible hypothesis
    // bool has_next = available_h.skipSkippables(solver, options.store_implicates, level);
    bool has_next = available_h.nextHypothesis(level);
    if (has_next) {
        solver.removeHypotheses(level);
        typename SolverT::HypothesisT& sel = available_h.getHypothesis();
        // Actual possible hypothesis
        solver.addHypothesis(sel, level);
        pushStackLevel();
    } else {
        // Actually no more hypotheses
        popStackLevel();
    }
}

/* ========== PID Algorithm ========== */

template<class SolverT>
extern void gpid::DecompositionEngine<SolverT>::generatePID() {
    resetEngine();

    while (level > 0) {
        if (sdir == IStackDirection::STACK_POP) {

            selectNextPID();

        } else {
            node_counter++;

            if (!options.allow_inconsistencies) {
                SolverTestStatus status = solver.checkConsistency(level);
                if (status == SolverTestStatus::SOLVER_UNSAT) {
                    incons_counter++;
                    popStackLevel();
                    continue;
                } else if (status == SolverTestStatus::SOLVER_UNKNOWN) {
                    l_fatal("Solver could not decide consistency query!");
                }
            }

            SolverTestStatus status = solver.testHypotheses(level);

            if (status == SolverTestStatus::SOLVER_SAT) {
                if (options.use_models) {
                    available_h.modelCleanUp(solver.recoverModel(), level);
                }
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
