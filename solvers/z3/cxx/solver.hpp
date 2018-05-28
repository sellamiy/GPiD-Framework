#ifndef GPID_Z3_SOLVER_INLINED_SPP
#define GPID_Z3_SOLVER_INLINED_SPP

namespace gpid {

    class Z3SolverInternal {
    public:
        z3::solver solver;
        Z3ModelWrapper iw_mdl;
        Z3SolverInternal(z3::context& ctx)
            : solver(ctx), iw_mdl(solver) { }
    };

    inline void Z3SolverInterface::push() { _internal->solver.push(); }

    inline void Z3SolverInterface::pop() { _internal->solver.pop(); }

    inline void Z3SolverInterface::addLiteral(Z3Literal& literal, bool negate) {
        _internal->solver.add(negate ? (!literal.expr) : literal.expr);
    }

    inline void Z3SolverInterface::addClause(HypothesisT& h, LiteralMapper<Z3Literal>& mapper,
                                             bool negate) {
        auto it = h.begin();
        z3::expr cl = mapper.get(*it).expr;
        if (negate) cl = !cl;
        while (++it != h.end()) {
            z3::expr ct = mapper.get(*it).expr;
            if (negate) ct = !ct;
            cl = cl || ct;
        }
        _internal->solver.add(cl);
    }

    inline Z3ModelWrapper& Z3SolverInterface::getModel() {
        return _internal->iw_mdl;
    }

    inline void Z3SolverInterface::printAssertions(bool negated) {
        p_implicate(std::cout, ctx, _internal->solver.assertions(), negated);
    }

    inline const std::string Z3SolverInterface::getPrintableAssertions(bool) {
        std::stringstream result;
        result << asformula(_internal->solver.assertions(), ctx);
        return result.str();
    }

    inline gpid::SolverTestStatus Z3SolverInterface::check() {
        z3::check_result qres = _internal->solver.check();
        switch (qres) {
        case z3::sat:   return SolverTestStatus::SAT;
        case z3::unsat: return SolverTestStatus::UNSAT;
        default:        return SolverTestStatus::UNKNOWN;
        }
    }

}

#endif
