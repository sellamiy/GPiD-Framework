/**
 * \file abdulot/ilinva/algorithm-ilinva.hpp
 * \brief Abdulot Framework Inductive Invariant Generator via Abduction.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__ALGORITHM_HPP
#define ABDULOT__ILINVA__ALGORITHM_HPP

#include <stack>

#include <abdulot/core/algorithm.hpp>
#include <abdulot/ilinva/iph-core.hpp>
#include <abdulot/ilinva/strengthener-dual.hpp>

namespace abdulot {
namespace ilinva {

    /**
     * \brief Inductive Invariant Generator via Abduction algorithm
     */
    template<typename EngineT>
    class IlinvaAlgorithm : public Algorithm {
    public:
        using StrengthenerT = typename EngineT::StrengthenerT;
    private:

        IlinvaOptions& options;
        EngineT pengine;

        using ProblemHandlerT = typename EngineT::ProblemHandlerT;

        using PropId = typename EngineT::PropIdentifierT;
        using StrengthenerId = typename StrengthenerT::IdentifierT;
        using level_ids_t = std::pair<PropId, StrengthenerId>;

        const DStrOptions dstren_opts;

        std::stack<level_ids_t> level_stack;
        std::stack<std::set<PropId>> tested_lids;

        void reset();
        void backtrack(bool force=false);
        virtual void _execute() override;

    public:
        /** Algorithm initialization */
        IlinvaAlgorithm(ProblemHandlerT& iph, AlgorithmOptions& opts, IlinvaOptions& iopts);

        /** Print informations on the algorithm and its parameters. */
        static void printInfos();

        const std::map<std::string, uint64_t> getEngineCounters() const;

    };

    /* *** Implementation *** */

    template<typename EngineT>
    IlinvaAlgorithm<EngineT>::
    IlinvaAlgorithm(ProblemHandlerT& iph, AlgorithmOptions& opts, IlinvaOptions& iopts)
        : Algorithm(opts),
          options(iopts),
          pengine(iph),
          dstren_opts(iopts)
    {}

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::printInfos() {
        snlog::l_message() << "Abdulot framework problem strengthener "
                           << project_version << snlog::l_end;
        snlog::l_message() << "Problem handler: " << snlog::l_end;
        ProblemHandlerT::printInfos();
    }

    template<typename EngineT>
    const std::map<std::string, uint64_t> IlinvaAlgorithm<EngineT>::getEngineCounters() const {
        return pengine.getCounters();
    }

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::reset() {
        snlog::l_warn() << "Not implemented: " << __FILE__ << " : " << __LINE__ << snlog::l_end;
    }

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::backtrack(bool force) {
        if (level_stack.empty())
            return;
        StrengthenerId strengthener = level_stack.top().second;
        if (force) {
            PropId prop = level_stack.top().first;
            pengine.release(prop);
        }
        while(!pengine.hasMoreStrengthenings(strengthener)) {
            PropId prop = level_stack.top().first;
            // pengine.release(prop);
            /*
            if (force) {
                force = false;
                if (pengine.hasMoreStrengthenings(strengthener)) {
                    break;
                }
            }
            */
            level_stack.pop();
            /* Check for other strengthenable props */
            if (!pengine.canGenerateVC(level_stack.size())) {
                /* Backtrack */
                if (level_stack.empty()) break;
                // Release once more
                PropId prop_t = level_stack.top().first;
                pengine.release(prop_t);
                strengthener = level_stack.top().second;
                // TODO: This is a hack to force internal cache removal
                //       This should be done in a better way.
                pengine.canGenerateVC(level_stack.size() - 1);
            } else {
                /* Try this other prop */
                PropId prop_t = pengine.selectUnprovenProp(level_stack.size());
                strengthener = pengine.newStrengthener(prop_t, dstren_opts, options.abd_override);
                level_stack.push(level_ids_t(prop_t, strengthener));
            }
        }
    }

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::_execute() {

        reset();

        bool assume_proven = false;
        PropId prop = -1; // Default (unselected) value
        StrengthenerId strengthener;

        while (!iflags.systemInterrupted()) {
            IphState iphState = pengine.proofCheck();

            if (iphState.proven) {
                assume_proven = true;
                break;
            }

            if (!iphState.strengthenable) {

                backtrack(true);

            } else if (level_stack.size() >= options.max_depth) {

                backtrack(true);

            } else {

                prop = pengine.selectUnprovenProp(level_stack.size());
                strengthener = pengine.newStrengthener(prop, dstren_opts, options.abd_override);
                level_stack.push(level_ids_t(prop, strengthener));
            }

            if (level_stack.empty()) {
                snlog::l_error() << "No more strengthening candidates available" << snlog::l_end;
                break;
            }

            if (!pengine.hasMoreStrengthenings(strengthener)) {
                backtrack();
            }

            // Rebreak here if necessary
            // TODO: Improve the structure of this loop, it is in beurk status
            if (level_stack.empty()) {
                snlog::l_error() << "No more strengthening candidates available" << snlog::l_end;
                break;
            }

            pengine.strengthen(level_stack.top());

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
}

#endif
