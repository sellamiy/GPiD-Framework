#define GPID_GENERATE_CPP

#include <DecompEngine.hpp>

template<class HypothesisT, class ProblemT, class SolverT>
extern void DecompositionEngine<HypothesisT, ProblemT, SolverT>::generateImplicates() {
    resetEngine();

    while (level > 0) {

        if (sdir == IStackDirection::STACK_POP) {

            if (!available_h.isEmpty(level)) {
                // Trying next hypothesis
                HypothesisT& sel = available_h.nextHypothesis(level);
                active_h.addHypothesis(sel, level);
                pushStackLevel();
            } else {
                // No more hypotheses here
                popStackLevel();
            }

        } else {

            SolverTestStatus status = solver.testHypotheses(active_h, level);
            if (status == SolverTestStatus::SOLVER_SAT) {
                // Adding an hypothesis
                HypothesisT& sel = available_h.nextHypothesis(level);
                active_h.addHypothesis(sel, level);
                pushStackLevel();
            } else if (status == SolverTestStatus::SOLVER_UNSAT) {
                // We have found an implicate
                activeIsImplicate();
                popStackLevel();
            } else {
                // Solver UNKNOWN :: ERROR
                // TODO: Notify
            }

        }

    }

}
