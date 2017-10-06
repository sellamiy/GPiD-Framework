#ifndef GPID_DECOMP_ENGINE_HPP
#define GPID_DECOMP_ENGINE_HPP

#include <stdint.h>
#include <vector>
#include <gpid/core/hypotheses.hpp>
#include <gpid/core/solvers.hpp>

namespace gpid {

    enum GenerationAlgorithm {
        BPD, PID
    };

    template <class HypothesisT, class ProblemT, class SolverT, class ModelT>
    class DecompositionEngine {

        enum IStackDirection {
            STACK_PUSH,
            STACK_POP
        };

        uint32_t level;
        IStackDirection sdir;

        SolverT& solver;
        ProblemT& problem;
        HypothesesSet<HypothesisT, ModelT>& available_h;

        void resetEngine();

        void activeIsImplicate();
        void printAsImplicate(std::vector<HypothesisT>& impl, bool negate=true);

        void pushStackLevel();
        void popStackLevel();

        void selectNextBPD();
        void generateBPD();

        void selectNextPID();
        void generatePID();

    public:
        DecompositionEngine(SolverT& s, ProblemT& p, HypothesesSet<HypothesisT, ModelT>& h)
            : solver(s), problem(p), available_h(h)
        { }

        void generateImplicates(GenerationAlgorithm algorithm = GenerationAlgorithm::PID);

    };

};

/* ========== Helpers ========== */

template<class HypothesisT, class ProblemT, class SolverT, class ModelT>
inline void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT, ModelT>::resetEngine() {
    solver.setProblem(problem);
    solver.start();
    level = 1;
    sdir = IStackDirection::STACK_PUSH;
}

template<class HypothesisT, class ProblemT, class SolverT, class ModelT>
inline void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT, ModelT>::activeIsImplicate() {
    // TODO: Handle More
    printAsImplicate(solver.extractActive());
}

template<class HypothesisT, class ProblemT, class SolverT, class ModelT>
inline void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT, ModelT>::pushStackLevel() {
    level++;
    sdir = IStackDirection::STACK_PUSH;
}

template<class HypothesisT, class ProblemT, class SolverT, class ModelT>
inline void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT, ModelT>::popStackLevel() {
    solver.removeHypotheses(level);
    level--;
    sdir = IStackDirection::STACK_POP;
}

template<class HypothesisT, class ProblemT, class SolverT, class ModelT>
inline void gpid::DecompositionEngine<HypothesisT, ProblemT, SolverT, ModelT>
::generateImplicates(gpid::GenerationAlgorithm algorithm) {
    switch (algorithm) {
    case BPD: generateBPD(); break;
    case PID: generatePID(); break;
    default: snlog::l_internal("Trying to generate implicates using unknown algorithm!");
    }
}

#endif
