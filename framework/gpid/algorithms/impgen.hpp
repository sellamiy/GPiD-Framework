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

    template<typename AbdEngineT>
    class ImpgenAlgorithm : public GPiDAlgorithm {

        ImpgenOptions& options;
        AbdEngineT lengine;

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
        ImpgenAlgorithm(ImpgenOptions& o);

        using ProblemLoaderT = typename AbdEngineT::ProblemLoaderT;

        /** \return The total number of implicates generated. */
        counter_t getGeneratedImplicatesCount() const;
        /** \return The total number of nodes explored during literals tries. */
        counter_t getExploredNodesCount() const;
    };

    /* *** Implementation *** */

    template<typename AbdEngineT>
    ImpgenAlgorithm<AbdEngineT>::ImpgenAlgorithm(ImpgenOptions& o)
        : options(o)
    { }

    template<typename AbdEngineT>
    inline GPiDAlgorithm::counter_t ImpgenAlgorithm<AbdEngineT>::getGeneratedImplicatesCount() const {
        return impl_counter;
    }

    template<typename AbdEngineT>
    inline GPiDAlgorithm::counter_t ImpgenAlgorithm<AbdEngineT>::getExploredNodesCount() const {
        return node_counter;
    }

    template<typename AbdEngineT>
    void ImpgenAlgorithm<AbdEngineT>::reset() {
        impl_counter = 0;
        node_counter = 0;
        level = 1;
        sdir = StackDirection::PUSH;
        lengine.setProblem();
        lengine.start();
        insthandle(instrument::idata(), instrument::instloc::reset);
    }

    template<typename AbdEngineT>
    void ImpgenAlgorithm<AbdEngineT>::notifyImplicate() {
        impl_counter++;
        if (options.print_implicates)
            lengine.printCurrentImplicate();
        if (options.store_implicates)
            lengine.storeCurrentImplicate();
        if (options.implicate_limit <= impl_counter)
            iflags.interrupt(SystemInterruptionFlags::Reason::SYS_INT_R__INTERNAL);
        insthandle(instrument::idata(), instrument::instloc::implicate);
    }

    template<typename AbdEngineT>
    void ImpgenAlgorithm<AbdEngineT>::push() {
        level++;
        sdir = StackDirection::PUSH;
        insthandle(instrument::idata(level), instrument::instloc::stack_push);
    }

    template<typename AbdEngineT>
    void ImpgenAlgorithm<AbdEngineT>::pop() {
        lengine.backtrack(level);
        level--;
        sdir = StackDirection::POP;
        insthandle(instrument::idata(level), instrument::instloc::stack_pop);
    }

    template<typename AbdEngineT>
    void ImpgenAlgorithm<AbdEngineT>::selectCandidate() {
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

    template<typename AbdEngineT>
    void ImpgenAlgorithm<AbdEngineT>::_execute() {

        reset();

        while (level > 0 && !iflags.systemInterrupted()) {
            if (sdir == StackDirection::STACK_POP) {

                selectCandidate();

            } else {
                node_counter++;

                SolverTestStatus status = lengine.testHypothesis(level);

                if (status == SolverTestStatus::SAT) {
                    if (options.use_models) {
                        lengine.modelCleanUp(level);
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
