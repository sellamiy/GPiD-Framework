#ifndef GPID_FRAMEWORK__CORE__ENGINE_HPP
#define GPID_FRAMEWORK__CORE__ENGINE_HPP

#include <cstdint>
#include <vector>
#include <gpid/options/options_engine.hpp>
#include <gpid/core/system.hpp>
#include <gpid/core/hypotheses.hpp>
#include <gpid/core/solvers.hpp>

namespace gpid {

    enum GenerationAlgorithm {
        PID
    };

    template <class SolverT>
    class DecompositionEngine {

        EngineOptions& options;
        SystemInterruptsFlags des_iflags;

        uint64_t gi_counter;
        uint64_t node_counter;

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

        void selectNextPID();
        void generatePID();

    public:
        DecompositionEngine(EngineOptions& o, SolverT& s, typename SolverT::ProblemT& p,
                            HypothesesSet<SolverT>& h)
            : options(o), solver(s), problem(p), available_h(h)
        { }
        inline uint64_t getGeneratedImplicatesCount()      const { return gi_counter;     }
        inline uint64_t getExploredNodesCount()            const { return node_counter;   }

        void generateImplicates(GenerationAlgorithm algorithm = GenerationAlgorithm::PID);
    };

};

/* ========== Helpers ========== */

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::resetEngine() {
    gi_counter = 0;
    node_counter = 0;
    solver.setProblem(problem);
    solver.start();
    level = 1;
    sdir = IStackDirection::STACK_PUSH;
    instrument::analyze(NULL, instrument::analyze_type::reset);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::activeIsImplicate() {
    gi_counter++;
    if (options.print_implicates)
        solver.printActiveNegation();
    if (options.store_implicates)
        solver.storeActive();
    instrument::analyze(NULL, instrument::analyze_type::implicate);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::pushStackLevel() {
    level++;
    sdir = IStackDirection::STACK_PUSH;
    instrument::analyze(&level, instrument::analyze_type::stack_push);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::popStackLevel() {
    solver.removeHypotheses(level);
    level--;
    sdir = IStackDirection::STACK_POP;
    instrument::analyze(&level, instrument::analyze_type::stack_pop);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>
::generateImplicates(gpid::GenerationAlgorithm algorithm) {
    registerInterruptsHandlers(&des_iflags);
    startTimeout(&des_iflags, options.time_limit);
    switch (algorithm) {
    case PID: generatePID(); break;
    default: snlog::l_internal("Trying to generate implicates using unknown algorithm!");
    }
    stopTimeout();
    restoreInterruptsHandlers();
    instrument::analyze(NULL, instrument::analyze_type::end);
}

#endif
