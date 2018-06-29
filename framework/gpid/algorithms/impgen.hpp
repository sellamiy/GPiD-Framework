/**
 * \file gpid/algorithms/impgen.hpp
 * \brief GPiD-Framework Implicate Generator via Decomposition.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__ALGORITHMS__IMPGEN_HPP
#define GPID_FRAMEWORK__ALGORITHMS__IMPGEN_HPP

#include <gpid/core/algorithm.hpp>
#include <gpid/core/errors.hpp>
#include <gpid/sai/saitypes.hpp>
#include <gpid/impgen/options.hpp>
#include <gpid/instrument/instrument.hpp>

namespace gpid {

    template<typename AbdEngineT, typename LiteralGeneratorT>
    class ImpgenAlgorithm : public GPiDAlgorithm {
    public:
        using ProblemLoaderT = typename AbdEngineT::ProblemLoaderT;
    private:

        ImpgenOptions& options;
        AbdEngineT lengine;
        ProblemLoaderT& pbloader;

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
        ImpgenAlgorithm(ProblemLoaderT& pbld, LiteralGeneratorT& lgen,
                        GPiDOptions& opts, ImpgenOptions& iopts);

        static void printInfos();

        /** \return The total number of implicates generated. */
        counter_t getGeneratedImplicatesCount() const;
        /** \return The total number of nodes explored during literals tries. */
        counter_t getExploredNodesCount() const;

        std::map<std::string, counter_t>& getSkippedCounts();
    };

    /* *** Implementation *** */

    template<typename AbdEngineT, typename LiteralGeneratorT>
    ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::
    ImpgenAlgorithm(ProblemLoaderT& pbld, LiteralGeneratorT& lgen,
                    GPiDOptions& opts, ImpgenOptions& iopts)
        : GPiDAlgorithm(opts),
          options(iopts),
          lengine(lgen, pbld.getContextManager(), iopts),
          pbloader(pbld)
    {}

    template<typename AbdEngineT, typename LiteralGeneratorT>
    void ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::printInfos() {
        snlog::l_warn("TODO: Better info printers");
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    inline GPiDAlgorithm::counter_t
    ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::getGeneratedImplicatesCount() const {
        return impl_counter;
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    inline GPiDAlgorithm::counter_t
    ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::getExploredNodesCount() const {
        return node_counter;
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    inline std::map<std::string, GPiDAlgorithm::counter_t>&
    ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::getSkippedCounts() {
        return lengine.getSkippedCounts();
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    void ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::reset() {
        impl_counter = 0;
        node_counter = 0;
        level = 1;
        sdir = StackDirection::PUSH;
        lengine.initializeSolvers(pbloader);
        lengine.reinit();
        insthandle(instrument::idata(), instrument::instloc::reset);
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    void ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::notifyImplicate() {
        impl_counter++;
        if (options.print_implicates)
            lengine.printCurrentImplicate();
        if (options.store_implicates)
            lengine.storeCurrentImplicate();
        if (options.implicate_limit <= impl_counter)
            iflags.interrupt(SystemInterruptionFlags::Reason::SYS_INT_R__INTERNAL);
        insthandle(instrument::idata(), instrument::instloc::implicate);
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    void ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::push() {
        level++;
        sdir = StackDirection::PUSH;
        insthandle(instrument::idata(level), instrument::instloc::stack_push);
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    void ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::pop() {
        lengine.backtrack(level);
        level--;
        sdir = StackDirection::POP;
        insthandle(instrument::idata(level), instrument::instloc::stack_pop);
    }

    template<typename AbdEngineT, typename LiteralGeneratorT>
    void ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::selectCandidate() {
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

    template<typename AbdEngineT, typename LiteralGeneratorT>
    void ImpgenAlgorithm<AbdEngineT, LiteralGeneratorT>::_execute() {

        reset();

        while (level > 0 && !iflags.systemInterrupted()) {
            if (sdir == StackDirection::POP) {

                selectCandidate();

            } else {
                node_counter++;

                SolverTestStatus status = lengine.testHypothesis(level);

                if (status == SolverTestStatus::SAT) {
                    if (options.use_models) {
                        lengine.modelCleanUp();
                    }
                    selectCandidate();
                } else if (status == SolverTestStatus::UNSAT) {
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
