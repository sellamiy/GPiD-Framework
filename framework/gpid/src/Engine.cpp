#define GPID_ENGINE_CPP

#include <DecompEngine.hpp>

using namespace gpid;

template<class HypothesisT, class ProblemT, class SolverT>
extern void DecompositionEngine<HypothesisT, ProblemT, SolverT>::resetEngine() {
    solver.setProblem(problem);
    solver.start();
    level = 1;
}

template<class HypothesisT, class ProblemT, class SolverT>
extern void DecompositionEngine<HypothesisT, ProblemT, SolverT>::activeIsImplicate() {
    // Means that active_h is unsat with the problem, thus that not(active_h) is an implicate
}

template<class HypothesisT, class ProblemT, class SolverT>
extern void DecompositionEngine<HypothesisT, ProblemT, SolverT>::pushStackLevel() {
    level++;
    sdir = IStackDirection::STACK_PUSH;
}

template<class HypothesisT, class ProblemT, class SolverT>
extern void DecompositionEngine<HypothesisT, ProblemT, SolverT>::popStackLevel() {
    solver.removeHypotheses(level);
    level--;
    sdir = IStackDirection::STACK_POP;
}
