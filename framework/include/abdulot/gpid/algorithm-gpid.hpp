/**
 * \file abdulot/gpid/algorithm-gpid.hpp
 * \brief Implicate Generator via Decomposition.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__GPID__ALGORITHM__GPID_HPP
#define ABDULOT__GPID__ALGORITHM__GPID_HPP

#include <abdulot/core/algorithm.hpp>
#include <abdulot/core/errors.hpp>
#include <abdulot/reference/version.hpp>
#include <abdulot/gpid/options.hpp>
#include <abdulot/gpid/implicates.hpp>
#include <abdulot/instrument/instrument.hpp>

namespace abdulot {
namespace gpid {

    /**
     * \brief Implicate generation via decompisition algorithm.
     *
     * Algorithmic instance of the implicate generator via decomposition
     * algorithm described in M. Echenim, N. Peltier, and Y. Sellami.
     * A generic framework for implicate generation modulo theories.
     * In Automated Reasoning, International Joint Conference, IJCAR 2018,
     * Proceedings, 2018.
     */
    template<typename EngineT, typename LitGenT, typename IHandlerT>
    class GPiDAlgorithm : public Algorithm {
    public:
        /** Problem loader type from the underlying engine. */
        using ProblemLoaderT = typename EngineT::ProblemLoaderT;
    private:

        GPiDOptions& options;
        EngineT lengine;
        ProblemLoaderT& pbloader;
        IHandlerT& imphandler;

        counter_t impl_counter;
        counter_t node_counter;

        enum class StackDirection { PUSH, POP };
        using level_t = uint32_t;

        level_t level;
        StackDirection sdir;

        void reset();
        void notifyImplicate();
        void push();
        void pop();

        void selectCandidate();
        virtual void _execute() override;

    public:
        /** Algorithm initialization */
        GPiDAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                      AlgorithmOptions& opts, GPiDOptions& iopts);
        GPiDAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                      AlgorithmOptions& opts, GPiDOptions& iopts,
                      typename EngineT::ExternalCheckerT& echecker);

        /** Print informations on the algorithm and its parameters. */
        static void printInfos();

        /** \return The total number of implicates generated. */
        counter_t getGeneratedImplicatesCount() const;
        /** \return The total number of nodes explored during literals tries. */
        counter_t getExploredNodesCount() const;

        /** \return The counts of skipped candidates for various reasons. */
        std::map<std::string, counter_t>& getSkippedCounts();

        EngineT& getEngine();
    };

    /* *** Implementation *** */

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::
    GPiDAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                  AlgorithmOptions& opts, GPiDOptions& iopts)
        : Algorithm(opts),
          options(iopts),
          lengine(lgen, pbld.getContextManager(), iopts),
          pbloader(pbld),
          imphandler(ihdl)
    {}

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::
    GPiDAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                  AlgorithmOptions& opts, GPiDOptions& iopts,
                  typename EngineT::ExternalCheckerT& echecker)
        : Algorithm(opts),
          options(iopts),
          lengine(lgen, pbld.getContextManager(), iopts, echecker),
          pbloader(pbld),
          imphandler(ihdl)
    {}

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    inline EngineT& GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::getEngine() {
        return lengine;
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::printInfos() {
        snlog::l_message() << "GPiD - framework implicate generator "
                           << project_version << snlog::l_end;
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    inline Algorithm::counter_t
    GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::getGeneratedImplicatesCount() const {
        return impl_counter;
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    inline Algorithm::counter_t
    GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::getExploredNodesCount() const {
        return node_counter;
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    inline std::map<std::string, Algorithm::counter_t>&
    GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::getSkippedCounts() {
        return lengine.getSkippedCounts();
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::reset() {
        impl_counter = 0;
        node_counter = 0;
        level = 1;
        sdir = StackDirection::PUSH;
        lengine.initializeSolvers(pbloader);
        lengine.reinit();
        insthandle(instrument::idata(), instrument::instloc::reset);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::notifyImplicate() {
        impl_counter++;
        imphandler(lengine);
        if (options.implicate_limit <= impl_counter)
            iflags.interrupt(SystemInterruptionFlags::Reason::__INTERNAL);
        insthandle(instrument::idata(), instrument::instloc::implicate);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::push() {
        level++;
        sdir = StackDirection::PUSH;
        insthandle(instrument::idata(level), instrument::instloc::stack_push);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::pop() {
        lengine.backtrack(level);
        level--;
        sdir = StackDirection::POP;
        insthandle(instrument::idata(level), instrument::instloc::stack_pop);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::selectCandidate() {
        // Recovering next possible literal
        bool has_next = lengine.searchNextLiteral(level);
        if (has_next) {
            lengine.backtrack(level);
            lengine.selectCurrentLiteral();
            push();
        } else {
            // Actually no more literals
            pop();
        }
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void GPiDAlgorithm<EngineT, LitGenT, IHandlerT>::_execute() {

        reset();

        if (options.preprune_literals)
            lengine.prepruneLiterals();

        while (level > 0 && !iflags.systemInterrupted()) {
            if (sdir == StackDirection::POP) {

                selectCandidate();

            } else {
                node_counter++;

                SolverTestStatus status = lengine.testHypothesis(level);

                if (isSatResult(status, options.unknown_handle)) {
                    if (options.use_models) {
                        lengine.modelCleanUp();
                    }
                    selectCandidate();
                } else if (isUnsatResult(status, options.unknown_handle)) {
                    // We have found an implicate
                    notifyImplicate();
                    pop();
                } else {
                    throw UndecidableProblemError("Solver could not decide query");
                }

            }

        }

        if (options.print_storage)  lengine.printStorage();
        if (options.export_storage) lengine.exportStorage(options.export_storage_location);
    }

}
}

#endif
