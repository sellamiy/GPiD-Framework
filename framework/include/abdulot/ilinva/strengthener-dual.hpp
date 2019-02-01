/**
 * \file abdulot/ilinva/strengthener-dual.hpp
 * \brief Dual Code-Interface condition abductive strengthener.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__DUAL_STRENGTHENER_HPP
#define ABDULOT__ILINVA__DUAL_STRENGTHENER_HPP

#include <stdutils/concurrent-containers.hpp>
#include <abdulot/gpid/algorithm-guniti.hpp>
#include <abdulot/gpid/engine-advanced.hpp>
#include <abdulot/gpid/algorithm-gpid.hpp>
#include <abdulot/ilinva/abdgen-dual.hpp>

namespace abdulot {
namespace ilinva {

    extern uint64_t StrengthenerIdCounter;
    static inline uint64_t nextStrengthenerId() {
        return StrengthenerIdCounter++;
    }

    struct DStrOptions {
        const bool disjunctions;
        const uint32_t sizelim;
        const uint64_t smt_tlim;

        explicit DStrOptions()
            : disjunctions(true), sizelim(1), smt_tlim(0)
        {}

        DStrOptions(bool disjunctions, uint32_t sizelim, uint64_t smt_tlim)
            : disjunctions(disjunctions), sizelim(sizelim), smt_tlim(smt_tlim)
        {}

        DStrOptions(const IlinvaOptions& iopts)
            : disjunctions(iopts.disjunct), sizelim(iopts.max_strengthening_size),
              smt_tlim(iopts.smt_time_limit)
        {}
    };

    template<typename CodeHandlerT, typename InterfaceT>
    class DualConditionStrengthener {
    public:
        using IdentifierT = uint64_t;
    private:

        const IdentifierT identifier;

        using CodeConstraintListT = std::list<typename CodeHandlerT::ConstraintT>;

        using ConstraintT = DualConstraintData<CodeHandlerT, InterfaceT, gpid::LiteralHypothesis>;

        using AbducibleEngine = gpid::AdvancedAbducibleEngine<InterfaceT>;

        class ImplicateForwarder;
        class ImplicateDisjunctor;

        class ImplicateForwarder {
            size_t reads;
            stdutils::ConcurrentVector<ConstraintT> implicants;

            typename InterfaceT::ContextManagerT& ictx;
            typename CodeHandlerT::ContextManagerT& ich_ctx;

            friend class ImplicateDisjunctor;
        public:
            ImplicateForwarder(typename InterfaceT::ContextManagerT& ictx,
                               typename CodeHandlerT::ContextManagerT& ich_ctx)
                : reads(0), ictx(ictx), ich_ctx(ich_ctx)
            {}

            inline bool isReadable() { return reads < implicants.size(); }
            // inline constexpr bool isWriteable() const { return !wlock; }

            inline void unhook() { }

            void operator()(AbducibleEngine& engine);
            ConstraintT nextImplicant();
        };

        class ImplicateDisjunctor {
            std::vector<ConstraintT> source;
            bool allowed;
            bool updated;
            size_t lid, rid;
        public:
            ImplicateDisjunctor(bool allowed=true) : allowed(allowed), updated(false) {}

            inline void update(ImplicateForwarder& fwder) {
                source = std::vector<ConstraintT>(fwder.implicants.extract());
                lid = 0; rid = 1;
                updated = true;
            }

            inline constexpr bool isUpdated() const { return updated; }

            inline bool canDisjunct() const { return allowed && (lid + 1 < source.size()); }
            ConstraintT nextImplicant();
        };

        using ImplicateGenerator =
            gpid::GPiDAlgorithm<AbducibleEngine,
                                SomehowSmartDualAbducibleGenerator<CodeHandlerT, InterfaceT>,
                                ImplicateForwarder>;

        AlgorithmOptions abductionCoreOpts;
        gpid::GPiDOptions abductionOpts;

        typename InterfaceT::ProblemLoaderT _problemBuilder;
        using AbdGeneratorT = SomehowSmartDualAbducibleGenerator<CodeHandlerT, InterfaceT>;
        using AbdGeneratorPtr = std::shared_ptr<AbdGeneratorT>;
        AbdGeneratorPtr abdGenerator;

        ImplicateForwarder forwarder;
        ImplicateDisjunctor disjunctor;
        using ImplicateGeneratorPtr = std::shared_ptr<ImplicateGenerator>;
        ImplicateGeneratorPtr generator;
    public:
        DualConditionStrengthener(const std::string& pfile, const CodeConstraintListT& cons,
                                  typename CodeHandlerT::ContextManagerT& ich_ctx,
                                  const DStrOptions& dopts=DStrOptions());
        ~DualConditionStrengthener();

        inline constexpr IdentifierT getId() const { return identifier; }

        inline bool hasMoreStrengthenings() {
            while (!generator->complete()) {
                if (forwarder.isReadable()) return true;
            }
            if (forwarder.isReadable())
                return true;
            if (!disjunctor.isUpdated()) {
                disjunctor.update(forwarder);
            }
            return disjunctor.canDisjunct();
        }

        inline ConstraintT nextCandidate() {
            if (forwarder.isReadable())
                return forwarder.nextImplicant();
            else
                return disjunctor.nextImplicant();
        }
    };

    /* *** Implementation *** */

    template<typename CodeHandlerT, typename InterfaceT>
    inline void DualConditionStrengthener<CodeHandlerT, InterfaceT>::ImplicateForwarder
    ::operator()(AbducibleEngine& engine) {
        implicants.store(ConstraintT(engine.getMapper(), engine.getCurrentImplicate(), ictx));
    }

    template<typename CodeHandlerT, typename InterfaceT>
    inline typename DualConditionStrengthener<CodeHandlerT, InterfaceT>::ConstraintT
    DualConditionStrengthener<CodeHandlerT, InterfaceT>::ImplicateForwarder::nextImplicant() {
        return implicants.access(reads++);
    }

    template<typename CodeHandlerT, typename InterfaceT>
    inline typename DualConditionStrengthener<CodeHandlerT, InterfaceT>::ConstraintT
    DualConditionStrengthener<CodeHandlerT, InterfaceT>::ImplicateDisjunctor::nextImplicant() {
        ConstraintT result = ConstraintT(CodeHandlerT::ConstraintT::disjunct(source[lid], source[rid]));
        rid++;
        if (rid >= source.size()) {
            rid = ++lid + 1;
        }
        return result;
    }

    template<typename CodeHandlerT, typename InterfaceT>
    DualConditionStrengthener<CodeHandlerT, InterfaceT>
    ::DualConditionStrengthener(const std::string& pfile, const CodeConstraintListT& cons,
                                typename CodeHandlerT::ContextManagerT& ich_ctx,
                                const DStrOptions& dopts)
        : identifier(nextStrengthenerId()),
          forwarder(_problemBuilder.getContextManager(), ich_ctx),
          disjunctor(dopts.disjunctions),
          generator(nullptr)
    {
        _problemBuilder.load(pfile, "smt2");
        abdGenerator =
            AbdGeneratorPtr(new AbdGeneratorT(cons, _problemBuilder.getContextManager()));
        abductionOpts.unknown_handle = SolverTestStatus::SAT;
        abductionOpts.max_level = dopts.sizelim + 1;
        abductionOpts.preprune_literals = true;
        abductionOpts.additional_checker = false; // Prevents non redundant literals
        abductionOpts.additional_check_mode = SolverTestStatus::SAT;
        abductionOpts.smt_time_limit = dopts.smt_tlim;
        generator =
            ImplicateGeneratorPtr(new ImplicateGenerator(_problemBuilder, *abdGenerator, forwarder,
                                                         abductionCoreOpts, abductionOpts));
        for (auto c_cons : ich_ctx.getCandidateConstraintDSplit()) {
            typename InterfaceT::LiteralT _addlit
                = convert<CodeHandlerT, InterfaceT>(c_cons, _problemBuilder.getContextManager());
            generator->getEngine().addAdditionalCheckLiteral(_addlit);
        }
        generator->execute(true);
    }

    template<typename CodeHandlerT, typename InterfaceT>
    DualConditionStrengthener<CodeHandlerT, InterfaceT>
    ::~DualConditionStrengthener() {
        forwarder.unhook();
        generator->interrupt();
        generator->join();
    }

}
}

#endif