/**
 * \file abdulot/ilinva/engine-dual.hpp
 * \brief Dual Code-Interface engine for inductive invariant generation via Abduction.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__DUAL_ENGINE_HPP
#define ABDULOT__ILINVA__DUAL_ENGINE_HPP

#include <abdulot/ilinva/ich-core.hpp>
#include <abdulot/ilinva/strengthener-dual.hpp>

namespace abdulot {
namespace ilinva {

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
        inline LoopIdentifierT selectUnprovenLoop(size_t id) {
            return sourceCode.selectUnprovenBlock(id);
        }

        StrengthenerId newStrengthener(LoopIdentifierT loop, const DStrOptions& dopts=DStrOptions(),
                                       const std::string& overrider=GPID_EMPTYSTR);

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
    (LoopIdentifierT loop, const DStrOptions& dopts, const std::string& overrider) {
        ++counters.strengtheners;
        auto loopCtx = sourceCode.generateContext(loop);
        std::shared_ptr<StrengthenerT>
            stren(new StrengthenerT(sourceCode.generateAbductionProblem(loop),
                                    sourceCode.generateSourceLiterals(loop, overrider), loopCtx, dopts));
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
}

#endif