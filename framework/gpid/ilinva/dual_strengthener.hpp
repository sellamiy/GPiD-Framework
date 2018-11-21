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
#include <gpid/ilinva/dual_data.hpp>
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

        class ImplicateForwarder {
            std::atomic<bool> readable;
            std::atomic<bool> writeable;

            typename InterfaceT::ContextManagerT& ictx;
            typename CodeHandlerT::ContextManagerT& ich_ctx;

            ConstraintT implicant;
        public:
            ImplicateForwarder(typename InterfaceT::ContextManagerT& ictx,
                               typename CodeHandlerT::ContextManagerT& ich_ctx)
                : readable(false), writeable(true), ictx(ictx), ich_ctx(ich_ctx),
                  implicant(CodeHandlerT::C_False)
            {}

            inline constexpr bool isReadable() const { return readable; }
            inline constexpr bool isWriteable() const { return writeable; }

            inline void unhook() { readable = true; writeable = true; }

            void operator()(AbducibleEngine& engine);
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
        using ImplicateGeneratorPtr = std::shared_ptr<ImplicateGenerator>;
        ImplicateGeneratorPtr generator;
    public:
        DualConditionStrengthener(const std::string& pfile, const CodeConstraintListT& cons,
                                  typename CodeHandlerT::ContextManagerT& ich_ctx);
        ~DualConditionStrengthener();

        inline constexpr IdentifierT getId() const { return identifier; }

        inline bool hasMoreStrengthenings() const {
            while (!generator->complete()) {
                if (forwarder.isReadable()) return true;
            }
            return false;
        }

        inline ConstraintT nextCandidate() {
            return forwarder.nextImplicant();
        }
    };

    /* *** Implementation *** */

    template<typename CodeHandlerT, typename InterfaceT>
    inline void DualConditionStrengthener<CodeHandlerT, InterfaceT>::ImplicateForwarder
    ::operator()(AbducibleEngine& engine) {
        while(!writeable);
        implicant = ConstraintT(engine.getMapper(), engine.getCurrentImplicate(), ictx, ich_ctx);
        writeable = false;
        readable = true;
    }

    template<typename CodeHandlerT, typename InterfaceT>
    inline typename DualConditionStrengthener<CodeHandlerT, InterfaceT>::ConstraintT
    DualConditionStrengthener<CodeHandlerT, InterfaceT>::ImplicateForwarder::nextImplicant() {
        while(!readable);
        ConstraintT result = implicant; // TODO: This copy is necessary for consistency
                                        //       Ensure that it is done
        readable = false;
        writeable = true;
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
        generator =
            ImplicateGeneratorPtr(new ImplicateGenerator(_problemBuilder, *abdGenerator, forwarder,
                                                         abductionCoreOpts, abductionOpts));
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
