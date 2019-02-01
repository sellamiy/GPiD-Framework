#ifndef MINISAT_PATCHED_INTERFACE_FOR_GPID__HPP
#define MINISAT_PATCHED_INTERFACE_FOR_GPID__HPP

#include <abdulot/core/saitypes.hpp>

#include "minisatp-context.hpp"
#include "minisatp-loaders.hpp"
#include "minisatp-abdgen.hpp"
#include "minisatp-printers.hpp"

namespace gpid {

    class MinisatInterface_Internal;

    class MinisatInterface {
        MinisatContextManager& ctx;
        const abdulot::SolverInterfaceOptions& siopts;
        Minisat::SimpSolver solver;
        MinisatModelWrapper iw_mdl;

        Minisat::vec<Minisat::Lit> assumps;
        std::vector<MinisatLiteral> loc_ass;
        Minisat::vec<int> lvl_stack;
    public:
        using ContextManagerT = MinisatContextManager;
        using ConstraintT = Minisat::vec<Minisat::Lit>&;
        using LiteralT = MinisatLiteral;
        using ModelT = MinisatModelWrapper;
        using ProblemLoaderT = MinisatProblemLoader;

        void push();
        void pop();
        void addLiteral(LiteralT& lit, bool negate=false);
        void addConstraint(ConstraintT cons);
        abdulot::SolverTestStatus check();
        ModelT& getModel();

        void printAssertions(bool negated);
        const std::string getPrintableAssertions(bool negated);

        template<typename ConjunctionIteratorGetter> static std::ostream& write
        (std::ostream& os, ContextManagerT& ctx, ConjunctionIteratorGetter& h,
         const abdulot::ObjectMapper<MinisatLiteral>& mapper, bool negate=false);

        template<typename ClauseIteratorGetter> void addClause
        (ClauseIteratorGetter& h, abdulot::ObjectMapper<LiteralT>& mapper, bool negate=false);
        void clearUnsafeClauses();

        MinisatInterface(MinisatContextManager& ctx, const abdulot::SolverInterfaceOptions& siopts);
        MinisatContextManager& getContextManager();
    };

    inline MinisatContextManager& MinisatInterface::getContextManager() { return ctx; }

    inline void MinisatInterface::push() {
        lvl_stack.push(assumps.size());
    }

    inline void MinisatInterface::pop() {
        while (assumps.size() > lvl_stack.last()) {
            assumps.pop();
            loc_ass.pop_back();
        }
        lvl_stack.pop(); // TODO: Check that this modification works after storage is reestablished
    }

    inline void MinisatInterface::addLiteral(MinisatLiteral& literal, bool negate) {
        loc_ass.push_back(literal);
        assumps.push(negate ? ~literal.lit : literal.lit);
    }

    inline void MinisatInterface::addConstraint(ConstraintT cons) {
        solver.addClause_(cons);
    }

    template<typename ClauseIteratorGetter>
    inline void MinisatInterface::addClause
    (ClauseIteratorGetter& h, abdulot::ObjectMapper<MinisatLiteral>& mapper, bool negate) {
        Minisat::vec<Minisat::Lit> ps;
        for (auto ml : h) {
            Minisat::Lit cl = mapper.get(ml).lit;
            ps.push(negate ? ~cl : cl);
        }
        solver.addClause_(ps);
    }

    template<typename ConjunctionIteratorGetter>
    inline std::ostream& MinisatInterface::write
    (std::ostream& os, ContextManagerT&, ConjunctionIteratorGetter& h,
     const abdulot::ObjectMapper<MinisatLiteral>& mapper, bool negate) {
        Minisat::vec<Minisat::Lit> ps;
        for (auto ml : h) {
            Minisat::Lit cl = mapper.get(ml).lit;
            ps.push(negate ? ~cl : cl);
        }
        return os << ps;
    }

    inline MinisatModelWrapper& MinisatInterface::getModel() {
        return iw_mdl;
    }

    inline void MinisatInterface::clearUnsafeClauses() {
        for (int i = 0; i < solver.clauses.size(); ++i) {
            auto ref = solver.clauses[i];
            solver.removeClause(ref);
        }
        solver.clauses.clear();
    }

    inline void MinisatInterface::printAssertions(bool negated) {
        p_implicate(std::cout, assumps, negated);
    }

    inline const std::string MinisatInterface::getPrintableAssertions(bool) {
        std::stringstream result;
        result << assumps;
        return result.str();
    }

    inline abdulot::SolverTestStatus MinisatInterface::check() {
        if (siopts.localTimeout > 0)
            snlog::l_warn() << "Minisat API interface does not handle check-call timeout yet"
                            << snlog::l_end;
        Minisat::lbool ret = solver.solveLimited(assumps);
        if      (ret == Minisat::l_True)  return abdulot::SolverTestStatus::SAT;
        else if (ret == Minisat::l_False) return abdulot::SolverTestStatus::UNSAT;
        else                              return abdulot::SolverTestStatus::UNKNOWN;
    }

}

#endif
