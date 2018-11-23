/**
 * \file gpid/ilinva/dual_strengthener.hpp
 * \brief Dual Code-Interface condition abductive strengthener.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__ILINVA__DUAL_STRENGTHENER_HPP
#define GPID_FRAMEWORK__ILINVA__DUAL_STRENGTHENER_HPP

#include <atomic>
#include <gpid/impgen/guniti_engine.hpp>
#include <gpid/impgen/guniti.hpp>
#include <gpid/impgen/advanced_engine.hpp>
#include <gpid/impgen/algorithm.hpp>
#include <gpid/ilinva/dual_ssag.hpp>

namespace gpid {

    extern uint64_t StrengthenerIdCounter;
    static inline uint64_t nextStrengthenerId() {
        return StrengthenerIdCounter++;
    }

    template<typename CodeHandlerT, typename InterfaceT>
    class DualConditionStrengthener {
    public:
        using IdentifierT = uint64_t;
    private:

        const IdentifierT identifier;

        using CodeConstraintListT = std::list<typename CodeHandlerT::ConstraintT>;

        using ConstraintT = DualConstraintData<CodeHandlerT, InterfaceT, LiteralHypothesis>;

        using AbducibleEngine = AdvancedAbducibleEngine<InterfaceT>;

        class ImplicateForwarder;
        class ImplicateDisjunctor;

        class ImplicateForwarder {
            std::atomic<bool> readable;
            std::atomic<bool> writeable;

            typename InterfaceT::ContextManagerT& ictx;
            typename CodeHandlerT::ContextManagerT& ich_ctx;

            friend class ImplicateDisjunctor;
            std::list<ConstraintT> implicants;
        public:
            ImplicateForwarder(typename InterfaceT::ContextManagerT& ictx,
                               typename CodeHandlerT::ContextManagerT& ich_ctx)
                : readable(false), writeable(true), ictx(ictx), ich_ctx(ich_ctx)
            {}

            inline constexpr bool isReadable() const { return readable; }
            inline constexpr bool isWriteable() const { return writeable; }

            inline void unhook() { readable = true; writeable = true; }

            void operator()(AbducibleEngine& engine);
            ConstraintT nextImplicant();
        };

        class ImplicateDisjunctor {
            std::vector<ConstraintT> source;
            bool updated;
            size_t lid, rid;
        public:
            ImplicateDisjunctor() : updated(false) {}

            inline void update(ImplicateForwarder& fwder) {
                source = std::vector<ConstraintT>(std::make_move_iterator(std::begin(fwder.implicants)),
                                                  std::make_move_iterator(std::end(fwder.implicants)));
                lid = 0; rid = 1;
                updated = true;
            }

            inline constexpr bool isUpdated() const { return updated; }

            inline bool canDisjunct() const { return lid + 1 < source.size(); }
            ConstraintT nextImplicant();
        };

        using ImplicateGenerator =
            ImpgenAlgorithm<AbducibleEngine,
                            SomehowSmartDualAbducibleGenerator<CodeHandlerT, InterfaceT>,
                            ImplicateForwarder>;

        GPiDOptions abductionCoreOpts;
        ImpgenOptions abductionOpts;

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
                                  typename CodeHandlerT::ContextManagerT& ich_ctx);
        ~DualConditionStrengthener();

        inline constexpr IdentifierT getId() const { return identifier; }

        inline bool hasMoreStrengthenings() {
            while (!generator->complete()) {
                if (forwarder.isReadable()) return true;
            }
            if (!disjunctor.isUpdated()) {
                disjunctor.update(forwarder);
            }
            return disjunctor.canDisjunct();
        }

        inline ConstraintT nextCandidate() {
            if (!generator->complete())
                return forwarder.nextImplicant();
            else
                return disjunctor.nextImplicant();
        }
    };

    /* *** Implementation *** */

    template<typename CodeHandlerT, typename InterfaceT>
    inline void DualConditionStrengthener<CodeHandlerT, InterfaceT>::ImplicateForwarder
    ::operator()(AbducibleEngine& engine) {
        while(!writeable);
        implicants.push_back(ConstraintT(engine.getMapper(), engine.getCurrentImplicate(), ictx));
        writeable = false;
        readable = true;
    }

    template<typename CodeHandlerT, typename InterfaceT>
    inline typename DualConditionStrengthener<CodeHandlerT, InterfaceT>::ConstraintT
    DualConditionStrengthener<CodeHandlerT, InterfaceT>::ImplicateForwarder::nextImplicant() {
        while(!readable);
        ConstraintT result = implicants.back();
        // TODO: This copy is necessary for consistency
        //       Ensure that it is done
        readable = false;
        writeable = true;
        return result;
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
                                typename CodeHandlerT::ContextManagerT& ich_ctx)
        : identifier(nextStrengthenerId()),
          forwarder(_problemBuilder.getContextManager(), ich_ctx),
          generator(nullptr)
    {
        _problemBuilder.load(pfile, "smt2");
        abdGenerator =
            AbdGeneratorPtr(new AbdGeneratorT(cons, _problemBuilder.getContextManager()));
        abductionOpts.unknown_handle = SolverTestStatus::SAT;
        abductionOpts.max_level = 2; // TODO: As ilinva option
        abductionOpts.preprune_literals = true;
        abductionOpts.additional_checker = true; // Prevents non redundant literals
        abductionOpts.additional_check_mode = SolverTestStatus::SAT;
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

#endif
