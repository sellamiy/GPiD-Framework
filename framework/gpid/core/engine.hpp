/**
 * \file gpid/core/engine.hpp
 * \brief GPiD-Framework Decomposition Engine.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__ENGINE_HPP
#define GPID_FRAMEWORK__CORE__ENGINE_HPP

#include <cstdint>
#include <vector>
#include <gpid/core/system.hpp>
#include <gpid/core/hypotheses.hpp>

namespace gpid {

    enum GenerationAlgorithm {
        PID
    };

    /** \brief Implicates generator. \ingroup gpidcorelib */
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
        /**
         * \brief Engine creation.
         * \param o Engine options.
         * \param s Solver interface for testint hypotheses.
         * \param p Problem to solve.
         * \param h Set of hypotheses to try.
         */
        DecompositionEngine(EngineOptions& o, SolverT& s, typename SolverT::ProblemT& p,
                            HypothesesSet<SolverT>& h)
            : options(o), solver(s), problem(p), available_h(h)
        { }
        /** \return The total number of implicates generated. */
        inline uint64_t getGeneratedImplicatesCount()      const { return gi_counter;     }
        /** \return The total number of nodes explored during hypotheses tries. */
        inline uint64_t getExploredNodesCount()            const { return node_counter;   }

        /** \brief Generate implicates for the given problem. */
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
    instrument::analyze(instrument::idata(), instrument::instloc::reset);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::activeIsImplicate() {
    gi_counter++;
    if (options.print_implicates)
        solver.printActiveNegation();
    if (options.store_implicates)
        solver.storeActive();
    if (options.implicate_limit <= gi_counter)
        des_iflags.interrupt(SystemInterruptsFlags::SYS_INT_R__INTERNAL);
    instrument::analyze(instrument::idata(), instrument::instloc::implicate);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::pushStackLevel() {
    level++;
    sdir = IStackDirection::STACK_PUSH;
    instrument::analyze(instrument::idata(level), instrument::instloc::stack_push);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>::popStackLevel() {
    solver.removeHypotheses(level);
    level--;
    sdir = IStackDirection::STACK_POP;
    instrument::analyze(instrument::idata(level), instrument::instloc::stack_pop);
}

template<class SolverT>
inline void gpid::DecompositionEngine<SolverT>
::generateImplicates(gpid::GenerationAlgorithm algorithm) {
    registerInterruptsHandlers(&des_iflags);
    startTimeout(&des_iflags, options.time_limit);
    switch (algorithm) {
    case PID: generatePID(); break;
    default: throw InternalError("Unknown generation algorithm");
    }
    stopTimeout();
    restoreInterruptsHandlers();
    instrument::analyze(instrument::idata(), instrument::instloc::end);
}

#endif
