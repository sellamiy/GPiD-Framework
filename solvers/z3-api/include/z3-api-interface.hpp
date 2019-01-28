#ifndef Z3_API_INTERFACE_FOR_GPID__HPP
#define Z3_API_INTERFACE_FOR_GPID__HPP

#include <gpid/core/saitypes.hpp>
#include "z3-api-context.hpp"
#include "z3-api-loaders.hpp"
#include "z3-api-printers.hpp"
#include "z3-api-abdgen.hpp"

namespace gpid {

    class Z3InterfaceAPI_Internal;

    class Z3InterfaceAPI {
        z3::context& ctx;
        const SolverInterfaceOptions& siopts;
        z3::solver solver;
        Z3ModelWrapper iw_mdl;
    public:
        using ContextManagerT = z3::context;
        using ConstraintT = z3::expr;
        using LiteralT = Z3Literal;
        using ModelT = Z3ModelWrapper;
        using ProblemLoaderT = Z3ProblemLoader;

        void push();
        void pop();
        void addLiteral(LiteralT& lit, bool negate=false);
        void addConstraint(ConstraintT cons);
        SolverTestStatus check();
        ModelT& getModel();

        void printAssertions(bool negated);
        const std::string getPrintableAssertions(bool negated);

        template<typename ConjunctionIteratorGetter> static std::ostream& write
        (std::ostream& os, ContextManagerT& ctx, ConjunctionIteratorGetter& h,
         const ObjectMapper<Z3Literal>& mapper, bool negate=false);

        template<typename ClauseIteratorGetter> void addClause
        (ClauseIteratorGetter& h, ObjectMapper<LiteralT>& mapper, bool negate=false);
        void clearUnsafeClauses();

        Z3InterfaceAPI(z3::context& ctx, const SolverInterfaceOptions& siopts);
        z3::context& getContextManager();
    };

    inline z3::context& Z3InterfaceAPI::getContextManager() { return ctx; }

    inline void Z3InterfaceAPI::push() { solver.push(); }

    inline void Z3InterfaceAPI::pop() { solver.pop(); }

    inline void Z3InterfaceAPI::addLiteral(Z3Literal& literal, bool negate) {
        solver.add(negate ? (!literal.expr) : literal.expr);
    }

    inline void Z3InterfaceAPI::addConstraint(ConstraintT cons) {
        solver.add(cons);
    }

    template<typename ClauseIteratorGetter>
    inline void Z3InterfaceAPI::addClause
    (ClauseIteratorGetter& h, ObjectMapper<Z3Literal>& mapper, bool negate) {
        auto it = h.begin();
        z3::expr cl = mapper.get(*it).expr;
        if (negate) cl = !cl;
        while (++it != h.end()) {
            z3::expr ct = mapper.get(*it).expr;
            if (negate) ct = !ct;
            cl = cl || ct;
        }
        solver.add(cl);
    }

    template<typename ConjunctionIteratorGetter>
    inline std::ostream& Z3InterfaceAPI::write
    (std::ostream& os, ContextManagerT&, ConjunctionIteratorGetter& h,
     const ObjectMapper<Z3Literal>& mapper, bool negate) {
        auto it = h.begin();
        z3::expr cl = mapper.get(*it).expr;
        while (++it != h.end()) {
            z3::expr ct = mapper.get(*it).expr;
            cl = cl && ct;
        }
        return os << (negate ? !cl : cl);
    }

    inline Z3ModelWrapper& Z3InterfaceAPI::getModel() {
        return iw_mdl;
    }

    inline void Z3InterfaceAPI::clearUnsafeClauses() { }

    inline void Z3InterfaceAPI::printAssertions(bool negated) {
        p_implicate(std::cout, ctx, solver.assertions(), negated);
    }

    inline const std::string Z3InterfaceAPI::getPrintableAssertions(bool) {
        std::stringstream result;
        result << asformula(solver.assertions(), ctx);
        return result.str();
    }

    inline gpid::SolverTestStatus Z3InterfaceAPI::check() {
        if (siopts.localTimeout > 0)
            snlog::l_warn() << "Z3 API interface does not handle check-call timeout yet"
                            << snlog::l_end;
        z3::check_result qres = solver.check();
        switch (qres) {
        case z3::sat:   return SolverTestStatus::SAT;
        case z3::unsat: return SolverTestStatus::UNSAT;
        default:        return SolverTestStatus::UNKNOWN;
        }
    }

}

#endif
