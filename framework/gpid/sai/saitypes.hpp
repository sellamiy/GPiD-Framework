/**
 * \file gpid/sai/saitypes.hpp
 * \brief GPiD-Framework Solver Abstraction Interface Types.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__SAI__SAI_TYPES_HPP
#define GPID_FRAMEWORK__SAI__SAI_TYPES_HPP

#include <map>
#include <iterator>
#include <starray/starray.hpp>

namespace gpid {

    /** \brief Generic Wrapper for Solver test results. \ingroup gpidcorelib */
    enum class SolverTestStatus {
        /** The formula is satisfiable */
        SAT,
        /** The formula is unsatisfiable */
        UNSAT,
        /** The formula satisfiability status cannot be computed */
        UNKNOWN
    };

    inline std::string to_string(const SolverTestStatus& s) {
        return s == SolverTestStatus::SAT
            ? "SAT"
            : s == SolverTestStatus::UNSAT
            ? "UNSAT"
            : "UNKNOWN";
    }

    template<typename CInterfaceT>
    class SolverInterfaceEngine {
    public:
        using InterfaceT = CInterfaceT;
        using ContextManagerT = typename InterfaceT::ContextManagerT;
        using LiteralT = typename InterfaceT::LiteralT;
        using ModelT = typename InterfaceT::ModelT;
    private:
        ContextManagerT _ctx;
        using interface_id_t = size_t;
        std::vector<InterfaceT*> _interfaces;

        inline interface_id_t createInterface();
        inline InterfaceT& getInterface(interface_id_t id) const;
    public:
        SolverInterfaceEngine();
        ~SolverInterfaceEngine();

        inline InterfaceT& newInterface();
        inline ContextManagerT& getContextManager() const;
    };

    /* *** Implementations *** */

    template<typename CInterfaceT>
    SolverInterfaceEngine<CInterfaceT>::SolverInterfaceEngine() { }

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
        _interfaces.push_back(new InterfaceT(_ctx));
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
