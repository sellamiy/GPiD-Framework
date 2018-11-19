/**
 * \file gpid/ilinva/algorithm.hpp
 * \brief GPiD-Framework Inductive Invariant Generator via Abduction.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__ILINVA__ALGORITHM_HPP
#define GPID_FRAMEWORK__ILINVA__ALGORITHM_HPP

#include <stack>

#include <gpid/core/algorithm.hpp>
#include <gpid/ilinva/options.hpp>
#include <gpid/instrument/instrument.hpp>

namespace gpid {

    /**
     * \brief Inductive Invariant Generator via Abduction algorithm
     */
    template<typename EngineT>
    class IlinvaAlgorithm : public GPiDAlgorithm {
    public:
        using StrengthenerT = typename EngineT::StrengthenerT;
    private:

        IlinvaOptions& options;
        EngineT pengine;

        using CodeHandlerT = typename EngineT::CodeHandlerT;

        using LoopId = typename EngineT::LoopIdentifierT;
        using StrengthenerId = typename StrengthenerT::IdentifierT;
        using level_ids_t = std::pair<LoopId, StrengthenerId>;
        std::stack<level_ids_t> level_stack;

        void reset();
        void backtrack();
        virtual void _execute() override;

    public:
        /** Algorithm initialization */
        IlinvaAlgorithm(CodeHandlerT& ich, GPiDOptions& opts, IlinvaOptions& iopts);

        /** Print informations on the algorithm and its parameters. */
        static void printInfos();

    };

    /* *** Implementation *** */

    template<typename EngineT>
    IlinvaAlgorithm<EngineT>::
    IlinvaAlgorithm(CodeHandlerT& ich, GPiDOptions& opts, IlinvaOptions& iopts)
        : GPiDAlgorithm(opts),
          options(iopts),
          pengine(ich)
    {}

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::printInfos() {
        snlog::l_message() << "GPiD framework loop invariant generator "
                           << project_version << snlog::l_end;
    }

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::reset() {
        snlog::l_warn() << "Not implemented: " << __FILE__ << " : " << __LINE__ << snlog::l_end;
    }

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::backtrack() {
        StrengthenerId strengthener = level_stack.top().second;
        while(!pengine.hasMoreStrengthenings(strengthener)) {
            LoopId loop = level_stack.top().first;
            pengine.release(loop);
            level_stack.pop();
            if (level_stack.empty()) break;
            strengthener = level_stack.top().second;
        }
    }

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::_execute() {

        reset();

        bool assume_proven = true;

        while (!pengine.isProven()) {

            LoopId loop = pengine.selectUnprovenLoop();
            StrengthenerId strengthener = pengine.newStrengthener(loop);
            level_stack.push(level_ids_t(loop, strengthener));

            if (pengine.hasMoreStrengthenings(strengthener)) {

                pengine.strengthen(level_stack.top());

            } else {

                backtrack();
                if (level_stack.empty()) {
                    assume_proven = false;
                    snlog::l_error() << "No more strengthening candidates available" << snlog::l_end;
                    break;
                }

                pengine.strengthen(level_stack.top());
            }

        }

        if (assume_proven) {
            if (options.output == "") {
                snlog::l_info() << "Writing results to stdout..." << snlog::l_end
                                << snlog::l_message << "invariants for the program..."
                                << snlog::l_end;
                pengine.getSourceHandler().exportSource(std::cout);
                snlog::l_message() << "---------------------" << snlog::l_end;
            } else {
                snlog::l_info() << "Writing results to " << options.output << snlog::l_end;
                pengine.getSourceHandler().exportSource(options.output);
            }
        } else {
            snlog::l_error() << "No invariants found" << snlog::l_end;
        }

    }

}

#endif
