#ifndef GPID_DECOMP_ENGINE_HPP
#define GPID_DECOMP_ENGINE_HPP

#include <cstdint>
#include <vector>
#include <gpid/options/options_engine.hpp>
#include <gpid/core/hypotheses.hpp>
#include <gpid/core/solvers.hpp>

namespace gpid {

    enum GenerationAlgorithm {
        BPD, PID
    };

    template <class SolverT>
    class DecompositionEngine {

        EngineOptions& options;

        uint64_t gi_counter;

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

        void pushStackLevel();
        void popStackLevel();

        void selectNextBPD();
        void generateBPD();

        void selectNextPID();
        void generatePID();

    public:
        DecompositionEngine(EngineOptions& o, SolverT& s, typename SolverT::ProblemT& p,
                            HypothesesSet<SolverT>& h)
            : options(o), solver(s), problem(p), available_h(h)
        { }
        inline uint64_t getGeneratedImplicatesCount() { return gi_counter; }

        void generateImplicates(GenerationAlgorithm algorithm = GenerationAlgorithm::PID);

    };

};

/* ========== Helpers ========== */

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::resetEngine() {
    gi_counter = 0;
    solver.setProblem(problem);
    solver.start();
    level = 1;
    sdir = IStackDirection::STACK_PUSH;
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::activeIsImplicate() {
    gi_counter++;
    if (options.print_implicates) {
        solver.printActiveNegation();
    }
    solver.storeActive();
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
