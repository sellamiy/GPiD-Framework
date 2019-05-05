/**
 * \file abdulot/core/saitypes.hpp
 * \brief Abdulot Framework Solver Abstraction Interface Types.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__CORE__SAI_TYPES_HPP
#define ABDULOT__CORE__SAI_TYPES_HPP

#include <map>
#include <vector>
#include <iterator>
#include <starray/starray.hpp>

namespace abdulot {

    /** Generic Wrapper for Solver test results. */
    enum class SolverTestStatus {
        /** The formula is satisfiable */
        SAT,
        /** The formula is unsatisfiable */
        UNSAT,
        /** The formula satisfiability status cannot be computed */
        UNKNOWN,
        ERROR
    };

    static inline constexpr bool isSatResult
    (SolverTestStatus status, SolverTestStatus sua) {
        return status == SolverTestStatus::SAT
            || (status == SolverTestStatus::UNKNOWN && sua == SolverTestStatus::SAT);
    }

    static inline constexpr bool isUnsatResult
    (SolverTestStatus status, SolverTestStatus sua) {
        return status == SolverTestStatus::UNSAT
            || (status == SolverTestStatus::UNKNOWN && sua == SolverTestStatus::UNSAT);
    }

    static inline constexpr bool isUnknownResult
    (SolverTestStatus status, SolverTestStatus sua) {
        return status == SolverTestStatus::UNKNOWN && sua == SolverTestStatus::UNKNOWN;
    }

    /** String converter for SolverTestStatus. */
    inline const std::string to_string(const SolverTestStatus& s) {
        return s == SolverTestStatus::SAT
            ? "SAT"
            : s == SolverTestStatus::UNSAT
            ? "UNSAT"
            : s == SolverTestStatus::UNKNOWN
            ? "UNKNOWN"
            : "ERROR"
            ;
    }

    struct SolverInterfaceOptions {
        const uint64_t localTimeout;
        const double smallLocalTimeout;

        const std::map<std::string, std::string> translationMap;
        const bool fullfwdTranslation;

        SolverInterfaceOptions
        (const std::map<std::string, std::string>& translationMap={}, bool fullfwdTranslation=false)
            : localTimeout(0), smallLocalTimeout(0), translationMap(translationMap),
              fullfwdTranslation(fullfwdTranslation)
        {}

        SolverInterfaceOptions
        (uint64_t localTimeout, const std::map<std::string, std::string>& translationMap={},
         bool fullfwdTranslation=false)
            : localTimeout(localTimeout), smallLocalTimeout(0), translationMap(translationMap),
              fullfwdTranslation(fullfwdTranslation)
        {}

        SolverInterfaceOptions
        (double smallLocalTimeout, const std::map<std::string, std::string>& translationMap={},
         bool fullfwdTranslation=false)
            : localTimeout(0), smallLocalTimeout(smallLocalTimeout), translationMap(translationMap),
              fullfwdTranslation(fullfwdTranslation)
        {}
    };

    /** Manager for handling multiple solver interfaces with a shared context. */
    template<typename CInterfaceT>
    class SolverInterfaceEngine {
    public:
        /** Interface type handled by the engine. */
        using InterfaceT = CInterfaceT;
        /** Context manager type of the handled interface type. */
        using ContextManagerT = typename InterfaceT::ContextManagerT;
        /** Literal type of the handled interface type. */
        using LiteralT = typename InterfaceT::LiteralT;
        /** Model type of the handled interface type. */
        using ModelT = typename InterfaceT::ModelT;
    private:
        ContextManagerT& _ctx;
        SolverInterfaceOptions _siopts;
        using interface_id_t = size_t;
        std::vector<InterfaceT*> _interfaces;

        inline interface_id_t createInterface();
        inline InterfaceT& getInterface(interface_id_t id) const;
    public:
        /** Initialization of the multi-interface handler. */
        SolverInterfaceEngine(ContextManagerT& ctx, const SolverInterfaceOptions& siopts);
        ~SolverInterfaceEngine();

        /** Initialize a new interface instance. */
        inline InterfaceT& newInterface();
        /** \return The underlying context manager. */
        inline ContextManagerT& getContextManager() const;
    };

    /* *** Implementations *** */

    template<typename CInterfaceT>
    SolverInterfaceEngine<CInterfaceT>::SolverInterfaceEngine
    (ContextManagerT& ctx, const SolverInterfaceOptions& siopts)
        : _ctx(ctx), _siopts(siopts) {}

    template<typename CInterfaceT>
    SolverInterfaceEngine<CInterfaceT>::~SolverInterfaceEngine() {
        for (InterfaceT* intp : _interfaces) {
            delete intp;
        }
    }

    template<typename CInterfaceT>
    inline typename SolverInterfaceEngine<CInterfaceT>::interface_id_t
    SolverInterfaceEngine<CInterfaceT>::createInterface() {
        interface_id_t nid = _interfaces.size();
        _interfaces.push_back(new InterfaceT(_ctx, _siopts));
        return nid;
    }

    template<typename CInterfaceT>
    inline CInterfaceT& SolverInterfaceEngine<CInterfaceT>::getInterface(interface_id_t id) const {
        return *(_interfaces[id]);
    }

    template<typename CInterfaceT>
    inline CInterfaceT& SolverInterfaceEngine<CInterfaceT>::newInterface() {
        return getInterface(createInterface());
    }

    template<typename CInterfaceT>
    inline typename CInterfaceT::ContextManagerT&
    SolverInterfaceEngine<CInterfaceT>::getContextManager() const {
        return _ctx;
    }
}

#endif
