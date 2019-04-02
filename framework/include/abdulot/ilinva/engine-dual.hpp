/**
 * \file abdulot/ilinva/engine-dual.hpp
 * \brief Dual Code-Interface engine for inductive invariant generation via Abduction.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__DUAL_ENGINE_HPP
#define ABDULOT__ILINVA__DUAL_ENGINE_HPP

#include <abdulot/ilinva/iph-core.hpp>
#include <abdulot/ilinva/strengthener-dual.hpp>

namespace abdulot {
namespace ilinva {

    static const std::string GPID_EMPTYSTR = "";

    template<typename FProblemHandlerT, typename InterfaceT>
    class DualInvariantEngine {
    public:
        using counter_t = uint64_t;

        using ProblemHandlerT = FProblemHandlerT;
        using PropIdentifierT = typename ProblemHandlerT::PropIdentifierT;
        using StrengthenerT = DualConditionStrengthener<ProblemHandlerT, InterfaceT>;
        using StrengthenerId = typename StrengthenerT::IdentifierT;
    private:
        ProblemHandlerT& ph;

        std::map<StrengthenerId, std::shared_ptr<StrengthenerT>> strengtheners;

        struct {
            counter_t pchecks = 0;
            counter_t strengthenings = 0;
            counter_t strengtheners = 0;
        } counters;

    public:
        DualInvariantEngine(ProblemHandlerT& source);

        inline IphState proofCheck() {
            ++counters.pchecks;
            return ph.proofCheck();
        }

        inline bool canGenerateVC(size_t id) {
            return ph.hasNextUnprovenBlock(id);
        }

        inline PropIdentifierT selectUnprovenProp(size_t id) {
            return ph.selectUnprovenBlock(id);
        }

        StrengthenerId newStrengthener(PropIdentifierT prop, const DStrOptions& dopts=DStrOptions(),
                                       const std::string& overrider=GPID_EMPTYSTR);

        inline bool hasMoreStrengthenings(StrengthenerId strengthener) const {
            return strengtheners.at(strengthener)->hasMoreStrengthenings();
        }

        void strengthen(PropIdentifierT prop, StrengthenerId strengthener);
        inline void strengthen(std::pair<PropIdentifierT, StrengthenerId> p) {
            strengthen(p.first, p.second);
        }

        inline void release(PropIdentifierT prop) {
            ph.release(prop);
        }

        inline ProblemHandlerT& getSourceHandler() const { return ph; }

        const std::map<std::string, uint64_t> getCounters() const;

    };

    /* *** Implementation *** */

    template<typename ProblemHandlerT, typename InterfaceT>
    DualInvariantEngine<ProblemHandlerT, InterfaceT>::DualInvariantEngine(ProblemHandlerT& source)
        : ph(source) {}

    template<typename ProblemHandlerT, typename InterfaceT>
    typename DualInvariantEngine<ProblemHandlerT, InterfaceT>::StrengthenerId
    DualInvariantEngine<ProblemHandlerT, InterfaceT>::newStrengthener
    (PropIdentifierT prop, const DStrOptions& dopts, const std::string& overrider) {
        ++counters.strengtheners;
        auto propCtx = ph.generateStrengheningContext(prop, overrider, dopts.shuffle);
        std::shared_ptr<StrengthenerT>
            stren(new StrengthenerT(propCtx, dopts));
        strengtheners[stren->getId()] = stren;
        return stren->getId();
    }

    template<typename ProblemHandlerT, typename InterfaceT>
    inline void DualInvariantEngine<ProblemHandlerT, InterfaceT>
    ::strengthen(PropIdentifierT prop, StrengthenerId strengthener) {
        ++counters.strengthenings;
        StrengthenerT& stren = *strengtheners[strengthener];
        ph.strengthen(prop, stren.nextCandidate());
    }

    template<typename ProblemHandlerT, typename InterfaceT>
    inline const std::map<std::string, uint64_t> DualInvariantEngine<ProblemHandlerT, InterfaceT>
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
