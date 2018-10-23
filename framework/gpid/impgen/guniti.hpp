/**
 * \file gpid/impgen/guniti.hpp
 * \brief GPiD-Framework Unit Implicate Generator via Decomposition.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__IMPGEN__GUNITI__ALGORITHM_HPP
#define GPID_FRAMEWORK__IMPGEN__GUNITI__ALGORITHM_HPP

#include <gpid/core/algorithm.hpp>
#include <gpid/core/errors.hpp>
#include <gpid/core/saitypes.hpp>
#include <gpid/impgen/options.hpp>
#include <gpid/impgen/guniti_engine.hpp>
#include <gpid/impgen/implicates.hpp>
#include <gpid/instrument/instrument.hpp>

namespace gpid {

    /**
     * \brief Unit implicate generation via decompisition algorithm.
     *
     * Specialized algorithmic instance of the implicate generation
     * algorithm described in M. Echenim, N. Peltier, and Y. Sellami.
     * A generic framework for implicate generation modulo theories.
     * In Automated Reasoning, International Joint Conference, IJCAR 2018,
     * Proceedings, 2018. for unit implicates.
     */
    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    class GunitiAlgorithm : public GPiDAlgorithm {
        using EngineT = GunitiEngine<InterfaceT>;
    public:
        /** Problem loader type from the underlying engine. */
        using ProblemLoaderT = typename InterfaceT::ProblemLoaderT;
    private:

        GunitiOptions& options;
        EngineT lengine;
        ProblemLoaderT& pbloader;
        IHandlerT& imphandler;

        counter_t impl_counter;

        void reset();
        void notifyImplicate();

        virtual void _execute() override;

    public:
        /** Algorithm initialization */
        GunitiAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                        GPiDOptions& opts, GunitiOptions& iopts);

        /** Print informations on the algorithm and its parameters. */
        static void printInfos();

        /** \return The total number of implicates generated. */
        counter_t getGeneratedImplicatesCount() const;

        /** \return The counts of skipped candidates for various reasons. */
        std::map<std::string, counter_t>& getSkippedCounts();
    };

    /* *** Implementation *** */

    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    GunitiAlgorithm<InterfaceT, LitGenT, IHandlerT>::
    GunitiAlgorithm(ProblemLoaderT& pbld, LitGenT& lgen, IHandlerT& ihdl,
                    GPiDOptions& opts, GunitiOptions& iopts)
        : GPiDAlgorithm(opts),
          options(iopts),
          lengine(lgen, pbld.getContextManager(), iopts),
          pbloader(pbld),
          imphandler(ihdl)
    {}

    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    void GunitiAlgorithm<InterfaceT, LitGenT, IHandlerT>::printInfos() {
        snlog::l_message() << "GPiD framework unit implicate generator "
                           << project_version << snlog::l_end;
    }

    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    inline GPiDAlgorithm::counter_t
    GunitiAlgorithm<InterfaceT, LitGenT, IHandlerT>::getGeneratedImplicatesCount() const {
        return impl_counter;
    }

    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    inline std::map<std::string, GPiDAlgorithm::counter_t>&
    GunitiAlgorithm<InterfaceT, LitGenT, IHandlerT>::getSkippedCounts() {
        return lengine.getSkippedCounts();
    }

    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    void GunitiAlgorithm<InterfaceT, LitGenT, IHandlerT>::reset() {
        impl_counter = 0;
        lengine.initializeSolvers(pbloader);
        lengine.reinit();
        insthandle(instrument::idata(), instrument::instloc::reset);
    }

    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    void GunitiAlgorithm<InterfaceT, LitGenT, IHandlerT>::notifyImplicate() {
        impl_counter++;
        imphandler(lengine);
        if (options.implicate_limit <= impl_counter)
            iflags.interrupt(SystemInterruptionFlags::Reason::__INTERNAL);
        insthandle(instrument::idata(), instrument::instloc::implicate);
    }

    template<typename InterfaceT, typename LitGenT, typename IHandlerT>
    void GunitiAlgorithm<InterfaceT, LitGenT, IHandlerT>::_execute() {

        reset();

        if (!options.allow_inconsistencies)
            lengine.prepruneInconsistentLiterals();

        // Model initialization
        SolverTestStatus status = lengine.testEmpty();
        bool complete = false;

        if (status == SolverTestStatus::SAT) {
            if (options.use_models) {
                lengine.modelCleanUp();
            }
        } else if (status == SolverTestStatus::UNSAT) {
            notifyImplicate();
            complete = true;
        } else {
            throw UndecidableProblemError("Solver could not decide query");
        }

        complete = !lengine.selectNextLiteral();

        while (!complete && !iflags.systemInterrupted()) {

            SolverTestStatus status = lengine.testCurrentLiteral();

            if (status == SolverTestStatus::UNSAT) {
                notifyImplicate();
            } else if (status == SolverTestStatus::UNKNOWN) {
                throw UndecidableProblemError("Solver could not decide query");
            }

            complete = !lengine.selectNextLiteral();
            
        }

        if (options.print_storage)  lengine.printStorage();
        if (options.export_storage) lengine.exportStorage(options.export_storage_location);
    }

}

#endif
