#ifndef GPID_GENERATION_ALGORITHMS_HPP
#define GPID_GENERATION_ALGORITHMS_HPP

#include <DecompEngine.hpp>

/* ========== Helpers ========== */

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::resetEngine() {
    solver.setProblem(problem);
    solver.start();
    level = 1;
}

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::activeIsImplicate() {
    // Means that active_h is unsat with the problem, thus that not(active_h) is an implicate
}

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::pushStackLevel() {
    level++;
    sdir = IStackDirection::STACK_PUSH;
}

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::popStackLevel() {
    solver.removeHypotheses(level);
    level--;
    sdir = IStackDirection::STACK_POP;
}

/* ========== Naive Algorithm ========== */

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::generateImplicates() {
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
                // Adding an hypothesis
                HypothesisT& sel = available_h.nextHypothesis(level);
                solver.addHypothesis(sel, level);
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

#endif
