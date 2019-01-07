/**
 * \file gpid/ilinva/dual_engine.hpp
 * \brief Dual Code-Interface engine for inductive invariant generation via Abduction.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__ILINVA__DUAL_ENGINE_HPP
#define GPID_FRAMEWORK__ILINVA__DUAL_ENGINE_HPP

#include <gpid/ilinva/coreich.hpp>
#include <gpid/ilinva/dual_strengthener.hpp>

namespace gpid {

    static const std::string GPID_EMPTYSTR = "";

    template<typename FCodeHandlerT, typename InterfaceT>
    class DualInvariantEngine {
    public:
        using counter_t = uint64_t;

        using CodeHandlerT = FCodeHandlerT;
        using LoopIdentifierT = typename CodeHandlerT::LoopIdentifierT;
        using StrengthenerT = DualConditionStrengthener<CodeHandlerT, InterfaceT>;
        using StrengthenerId = typename StrengthenerT::IdentifierT;
    private:
        CodeHandlerT& sourceCode;

        std::map<StrengthenerId, std::shared_ptr<StrengthenerT>> strengtheners;

        struct {
            counter_t pchecks = 0;
            counter_t strengthenings = 0;
            counter_t strengtheners = 0;
        } counters;

    public:
        DualInvariantEngine(CodeHandlerT& source);

        inline IchState proofCheck() {
            ++counters.pchecks;
            return sourceCode.proofCheck();
        }
        inline LoopIdentifierT selectUnprovenLoop() {
            return sourceCode.selectUnprovenBlock();
        }

        StrengthenerId newStrengthener(LoopIdentifierT loop, const std::string& overrider=GPID_EMPTYSTR);
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

        const std::map<std::string, uint64_t> getCounters() const;

    };

    /* *** Implementation *** */

    template<typename CodeHandlerT, typename InterfaceT>
    DualInvariantEngine<CodeHandlerT, InterfaceT>::DualInvariantEngine(CodeHandlerT& source)
        : sourceCode(source) {}

    template<typename CodeHandlerT, typename InterfaceT>
    typename DualInvariantEngine<CodeHandlerT, InterfaceT>::StrengthenerId
    DualInvariantEngine<CodeHandlerT, InterfaceT>::newStrengthener
    (LoopIdentifierT loop, const std::string& overrider) {
        ++counters.strengtheners;
        auto loopCtx = sourceCode.generateContext(loop);
        std::shared_ptr<StrengthenerT>
            stren(new StrengthenerT(sourceCode.generateAbductionProblem(loop),
                                    sourceCode.generateSourceLiterals(loop, overrider), loopCtx));
        strengtheners[stren->getId()] = stren;
        return stren->getId();
    }

    template<typename CodeHandlerT, typename InterfaceT>
    inline void DualInvariantEngine<CodeHandlerT, InterfaceT>
    ::strengthen(LoopIdentifierT loop, StrengthenerId strengthener) {
        ++counters.strengthenings;
        StrengthenerT& stren = *strengtheners[strengthener];
        sourceCode.strengthen(loop, stren.nextCandidate());
    }

    template<typename CodeHandlerT, typename InterfaceT>
    inline const std::map<std::string, uint64_t> DualInvariantEngine<CodeHandlerT, InterfaceT>
    ::getCounters() const {
        std::map<std::string, uint64_t> results;
        results["code proofs"]    = counters.pchecks;
        results["strengthenings"] = counters.strengthenings;
        results["strengtheners"]  = counters.strengtheners;
        return results;
    }

}

#endif
