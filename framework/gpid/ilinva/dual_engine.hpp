/**
 * \file gpid/ilinva/dual_engine.hpp
 * \brief Dual Code-Interface engine for inductive invariant generation via Abduction.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__ILINVA__DUAL_ENGINE_HPP
#define GPID_FRAMEWORK__ILINVA__DUAL_ENGINE_HPP

#include <gpid/ilinva/dual_strengthener.hpp>
#include <gpid/instrument/instrument.hpp>

namespace gpid {

    template<typename FCodeHandlerT, typename InterfaceT>
    class DualInvariantEngine {
    public:
        using CodeHandlerT = FCodeHandlerT;
        using LoopIdentifierT = typename CodeHandlerT::LoopIdentifierT;
        using StrengthenerT = DualConditionStrengthener<CodeHandlerT, InterfaceT>;
        using StrengthenerId = typename StrengthenerT::IdentifierT;
    private:
        CodeHandlerT& sourceCode;

        std::map<StrengthenerId, std::shared_ptr<StrengthenerT>> strengtheners;

    public:
        DualInvariantEngine(CodeHandlerT& source);

        inline bool isProven() { return sourceCode.isProven(); }
        inline LoopIdentifierT selectUnprovenLoop() {
            return sourceCode.selectUnprovenBlock();
        }

        StrengthenerId newStrengthener(LoopIdentifierT loop);
        inline bool hasMoreStrengthenings(StrengthenerId strengthener) const {
            return strengtheners.at(strengthener)->hasMoreStrengthenings();
        }

        void strengthen(LoopIdentifierT loop, StrengthenerId strengthener);
        inline void strengthen(std::pair<LoopIdentifierT, StrengthenerId> p) {
            strengthen(p.first, p.second);
        }

        inline void release(LoopIdentifierT loop) {
            sourceCode.release(loop);
        }

        inline CodeHandlerT& getSourceHandler() const { return sourceCode; }

    };

    /* *** Implementation *** */

    template<typename CodeHandlerT, typename InterfaceT>
    DualInvariantEngine<CodeHandlerT, InterfaceT>::DualInvariantEngine(CodeHandlerT& source)
        : sourceCode(source) {}

    template<typename CodeHandlerT, typename InterfaceT>
    typename DualInvariantEngine<CodeHandlerT, InterfaceT>::StrengthenerId
    DualInvariantEngine<CodeHandlerT, InterfaceT>::newStrengthener(LoopIdentifierT loop) {
        auto loopCtx = sourceCode.generateContext(loop);
        std::shared_ptr<StrengthenerT>
            stren(new StrengthenerT(sourceCode.generateAbductionProblem(loop),
                                    sourceCode.generateSourceLiterals(loop), loopCtx));
        strengtheners[stren->getId()] = stren;
        return stren->getId();
    }

    template<typename CodeHandlerT, typename InterfaceT>
    inline void DualInvariantEngine<CodeHandlerT, InterfaceT>
    ::strengthen(LoopIdentifierT loop, StrengthenerId strengthener) {
        StrengthenerT& stren = *strengtheners[strengthener];
        sourceCode.strengthen(loop, stren.nextCandidate());
    }

}

#endif
