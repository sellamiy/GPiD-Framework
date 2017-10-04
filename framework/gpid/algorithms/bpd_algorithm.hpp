#ifndef GPID_GENERATION_ALGORITHMS_HPP
#define GPID_GENERATION_ALGORITHMS_HPP

#include <snlog/snlog.hpp>
#include <gpid/core/engine.hpp>

using namespace snlog;

/* ========== Helpers ========== */

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::resetEngine() {
    solver.setProblem(problem);
    solver.start();
    level = 1;
    sdir = IStackDirection::STACK_PUSH;
}

template<class HypothesisT, class ProblemT, class SolverT>
extern void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT>::activeIsImplicate() {
    // TODO: Handle More
    printAsImplicate(solver.extractActive());
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

/* ========== BPD Algorithm ========== */

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
