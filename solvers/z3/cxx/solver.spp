#ifndef GPID_Z3_SOLVER_INLINED_SPP
#define GPID_Z3_SOLVER_INLINED_SPP

namespace gpid {

    class Z3SolverInternal {
    public:
        z3::solver solver;
        z3::solver csty_solver;
        Z3ModelWrapper iw_mdl;

        Z3SolverInternal(z3::context& ctx)
            : solver(ctx), csty_solver(ctx), iw_mdl(solver)
        { }
    };

    inline void Z3Solver::accessLevel(uint32_t level) {
        while (level > c_level) {
            solvers->solver.push();
            solvers->csty_solver.push();
            c_level++;
        }
        while (level < c_level) {
            solvers->solver.pop();
            solvers->csty_solver.pop();
            c_level--;
        }
    }

    inline void Z3Solver::addHypothesis(Z3Hypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        solvers->solver.add(hypothesis.expr);
        solvers->csty_solver.add(hypothesis.expr);
    }

    inline void Z3Solver::removeHypotheses(uint32_t level) {
        accessLevel(level - 1);
        accessLevel(level);
    }

    inline Z3ModelWrapper& Z3Solver::recoverModel() {
        return solvers->iw_mdl;
    }

    inline void Z3Solver::printActiveNegation() {
        p_implicate(std::cout, ctx, solvers->csty_solver.assertions(), true);
    }

    inline void Z3Solver::storeActive() {
        snlog::l_warn("Not implemented yet - Z3 active storage");
    }

    inline gpid::SolverTestStatus Z3Solver::testHypotheses(uint32_t level) {
        accessLevel(level);
        z3::check_result qres = solvers->solver.check();
        switch (qres) {
        case z3::sat:   return SolverTestStatus::SOLVER_SAT;
        case z3::unsat: return SolverTestStatus::SOLVER_UNSAT;
        default:        return SolverTestStatus::SOLVER_UNKNOWN;
        }
    }

    inline gpid::SolverTestStatus Z3Solver::checkConsistency(uint32_t level) {
        accessLevel(level);
        z3::check_result qres = solvers->csty_solver.check();
        switch (qres) {
        case z3::sat:   return SolverTestStatus::SOLVER_SAT;
        case z3::unsat: return SolverTestStatus::SOLVER_UNSAT;
        default:        return SolverTestStatus::SOLVER_UNKNOWN;
        }
    }

    inline bool Z3Solver::storageSubsumed(Z3Hypothesis&, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - Z3 storage subsumption");
        return false;
    }

};

#endif
