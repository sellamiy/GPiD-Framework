/**
 * \file gpid/impgen/algorithm.hpp
 * \brief GPiD-Framework Implicate Generator via Decomposition.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__IMPGEN__ALGORITHM_HPP
#define GPID_FRAMEWORK__IMPGEN__ALGORITHM_HPP

#include <gpid/core/algorithm.hpp>
#include <gpid/core/errors.hpp>
#include <gpid/core/saitypes.hpp>
#include <gpid/reference/version.hpp>
#include <gpid/impgen/options.hpp>
#include <gpid/impgen/implicates.hpp>
#include <gpid/instrument/instrument.hpp>

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
    class ImpgenAlgorithm : public GPiDAlgorithm {
    public:
        /** Problem loader type from the underlying engine. */
        using ProblemLoaderT = typename EngineT::ProblemLoaderT;
    private:

        ImpgenOptions& options;
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
        ImpgenAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                        GPiDOptions& opts, ImpgenOptions& iopts);

        /** Print informations on the algorithm and its parameters. */
        static void printInfos();

        /** \return The total number of implicates generated. */
        counter_t getGeneratedImplicatesCount() const;
        /** \return The total number of nodes explored during literals tries. */
        counter_t getExploredNodesCount() const;

        /** \return The counts of skipped candidates for various reasons. */
        std::map<std::string, counter_t>& getSkippedCounts();
    };

    /* *** Implementation *** */

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::
    ImpgenAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                    GPiDOptions& opts, ImpgenOptions& iopts)
        : GPiDAlgorithm(opts),
          options(iopts),
          lengine(lgen, pbld.getContextManager(), iopts),
          pbloader(pbld),
          imphandler(ihdl)
    {}

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::printInfos() {
        snlog::l_message() << "GPiD framework implicate generator "
                           << project_version << snlog::l_end;
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    inline GPiDAlgorithm::counter_t
    ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::getGeneratedImplicatesCount() const {
        return impl_counter;
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    inline GPiDAlgorithm::counter_t
    ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::getExploredNodesCount() const {
        return node_counter;
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    inline std::map<std::string, GPiDAlgorithm::counter_t>&
    ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::getSkippedCounts() {
        return lengine.getSkippedCounts();
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::reset() {
        impl_counter = 0;
        node_counter = 0;
        level = 1;
        sdir = StackDirection::PUSH;
        lengine.initializeSolvers(pbloader);
        lengine.reinit();
        insthandle(instrument::idata(), instrument::instloc::reset);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::notifyImplicate() {
        impl_counter++;
        imphandler(lengine);
        if (options.implicate_limit <= impl_counter)
            iflags.interrupt(SystemInterruptionFlags::Reason::__INTERNAL);
        insthandle(instrument::idata(), instrument::instloc::implicate);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::push() {
        level++;
        sdir = StackDirection::PUSH;
        insthandle(instrument::idata(level), instrument::instloc::stack_push);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::pop() {
        lengine.backtrack(level);
        level--;
        sdir = StackDirection::POP;
        insthandle(instrument::idata(level), instrument::instloc::stack_pop);
    }

    template<typename EngineT, typename LitGenT, typename IHandlerT>
    void ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::selectCandidate() {
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
    void ImpgenAlgorithm<EngineT, LitGenT, IHandlerT>::_execute() {

        reset();

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

#endif
