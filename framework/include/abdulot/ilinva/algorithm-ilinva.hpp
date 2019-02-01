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
#include <abdulot/ilinva/ich-core.hpp>
#include <abdulot/ilinva/options.hpp>
#include <abdulot/ilinva/strengthener-dual.hpp>
#include <abdulot/instrument/instrument.hpp>

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

        using CodeHandlerT = typename EngineT::CodeHandlerT;

        using LoopId = typename EngineT::LoopIdentifierT;
        using StrengthenerId = typename StrengthenerT::IdentifierT;
        using level_ids_t = std::pair<LoopId, StrengthenerId>;

        const DStrOptions dstren_opts;

        std::stack<level_ids_t> level_stack;
        std::stack<std::set<LoopId>> tested_lids;

        void reset();
        void backtrack();
        virtual void _execute() override;

    public:
        /** Algorithm initialization */
        IlinvaAlgorithm(CodeHandlerT& ich, AlgorithmOptions& opts, IlinvaOptions& iopts);

        /** Print informations on the algorithm and its parameters. */
        static void printInfos();

        const std::map<std::string, uint64_t> getEngineCounters() const;

    };

    /* *** Implementation *** */

    template<typename EngineT>
    IlinvaAlgorithm<EngineT>::
    IlinvaAlgorithm(CodeHandlerT& ich, AlgorithmOptions& opts, IlinvaOptions& iopts)
        : Algorithm(opts),
          options(iopts),
          pengine(ich),
          dstren_opts(iopts)
    {}

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::printInfos() {
        snlog::l_message() << "GPiD framework loop invariant generator "
                           << project_version << snlog::l_end;
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
    void IlinvaAlgorithm<EngineT>::backtrack() {
        StrengthenerId strengthener = level_stack.top().second;
        while(!pengine.hasMoreStrengthenings(strengthener)) {
            LoopId loop = level_stack.top().first;
            pengine.release(loop);
            level_stack.pop();
            /* Check for other strengthenable loops */
            LoopId loop_t = pengine.selectUnprovenLoop(level_stack.size());
            if (stdutils::inset(tested_lids.top(), loop_t)) {
                /* Backtrack */
                tested_lids.pop();
                if (level_stack.empty()) break;
                strengthener = level_stack.top().second;
            } else {
                /* Try this other loop */
                strengthener = pengine.newStrengthener(loop_t, dstren_opts, options.abd_override);
                level_stack.push(level_ids_t(loop_t, strengthener));
                tested_lids.top().insert(loop_t);
            }
        }
    }

    template<typename EngineT>
    void IlinvaAlgorithm<EngineT>::_execute() {

        reset();

        bool assume_proven = false;
        LoopId loop = -1; // Default (unselected) value
        StrengthenerId strengthener;

        while (!iflags.systemInterrupted()) {
            IchState ichState = pengine.proofCheck();

            if (ichState.proven) {
                assume_proven = true;
                break;
            }

            if (!ichState.strengthenable)
                goto prebacktrack;

            if (level_stack.size() >= options.max_depth)
                goto prebacktrack;

            loop = pengine.selectUnprovenLoop(level_stack.size());
            strengthener = pengine.newStrengthener(loop, dstren_opts, options.abd_override);
            level_stack.push(level_ids_t(loop, strengthener));
            tested_lids.push({ loop });

            if (pengine.hasMoreStrengthenings(strengthener))
                pengine.strengthen(level_stack.top());
            else
                goto backtrack;

            continue;

        prebacktrack:
            pengine.release(loop);
        backtrack:
            backtrack();

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
