#ifndef GPID_DECOMP_ENGINE_HPP
#define GPID_DECOMP_ENGINE_HPP

#include <stdint.h>
#include <Hypotheses.hpp>
#include <AbstractSolver.hpp>

template <class HypothesisT, class ProblemT, class SolverT>
class DecompositionEngine {

    enum IStackDirection {
        STACK_PUSH,
        STACK_POP
    };

    uint32_t level;
    IStackDirection sdir;

    SolverT& solver;
    ProblemT& problem;
    HypothesesSet<HypothesisT> active_h;
    HypothesesSet<HypothesisT> available_h;

    void resetEngine();

    void activeIsImplicate();

    void pushStackLevel();
    void popStackLevel();

public:
    DecompositionEngine(SolverT& s, ProblemT& p, HypothesesSet<HypothesisT>& h)
        : solver(s), problem(p), available_h(h)
    { }

    void generateImplicates();

};

#endif
