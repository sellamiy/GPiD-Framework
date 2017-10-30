#ifndef GPID_DECOMP_ENGINE_HPP
#define GPID_DECOMP_ENGINE_HPP

#include <cstdint>
#include <vector>
#include <gpid/options/options_engine.hpp>
#include <gpid/core/hypotheses.hpp>
#include <gpid/core/solvers.hpp>

namespace gpid {

    enum GenerationAlgorithm {
        PID
    };

    template <class SolverT>
    class DecompositionEngine {

        EngineOptions& options;

        uint64_t gi_counter;
        uint64_t node_counter;
        uint64_t incons_counter;

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
        inline uint64_t getGeneratedImplicatesCount() { return gi_counter; }

        void generateImplicates(GenerationAlgorithm algorithm = GenerationAlgorithm::PID);

        void printStatistics();
    };

};

/* ========== Printers ========== */

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::printStatistics() {
    snlog::l_notif("implicates generated", gi_counter);
    snlog::l_notif("nodes explored", node_counter);
    snlog::l_notif("inconsistent implicates skipped", incons_counter);
}

/* ========== Helpers ========== */

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::resetEngine() {
    gi_counter = 0;
    node_counter = 0;
    incons_counter = 0;
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
    switch (algorithm) {
    case PID: generatePID(); break;
    default: snlog::l_internal("Trying to generate implicates using unknown algorithm!");
    }
    instrument::analyze(NULL, instrument::analyze_type::end);
}

#endif
