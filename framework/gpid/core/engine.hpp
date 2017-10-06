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

    template <class SolverT>
    class DecompositionEngine {

        enum IStackDirection {
            STACK_PUSH,
            STACK_POP
        };

        uint32_t level;
        IStackDirection sdir;

        SolverT& solver;
        typename SolverT::ProblemT& problem;
        HypothesesSet<SolverT>& available_h;

        void resetEngine();

        void activeIsImplicate();
        void printAsImplicate(std::vector<typename SolverT::HypothesisT>& impl, bool negate=true);

        void pushStackLevel();
        void popStackLevel();

        void selectNextBPD();
        void generateBPD();

        void selectNextPID();
        void generatePID();

    public:
        DecompositionEngine(SolverT& s, typename SolverT::ProblemT& p, HypothesesSet<SolverT>& h)
            : solver(s), problem(p), available_h(h)
        { }

        void generateImplicates(GenerationAlgorithm algorithm = GenerationAlgorithm::PID);

    };

};

/* ========== Helpers ========== */

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::resetEngine() {
    solver.setProblem(problem);
    solver.start();
    level = 1;
    sdir = IStackDirection::STACK_PUSH;
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::activeIsImplicate() {
    // TODO: Handle More
    printAsImplicate(solver.extractActive());
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::pushStackLevel() {
    level++;
    sdir = IStackDirection::STACK_PUSH;
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::popStackLevel() {
    solver.removeHypotheses(level);
    level--;
    sdir = IStackDirection::STACK_POP;
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>
::generateImplicates(gpid::GenerationAlgorithm algorithm) {
    switch (algorithm) {
    case BPD: generateBPD(); break;
    case PID: generatePID(); break;
    default: snlog::l_internal("Trying to generate implicates using unknown algorithm!");
    }
}

#endif
