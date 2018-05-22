#ifndef GPID_Z3_SOLVER_INLINED_SPP
#define GPID_Z3_SOLVER_INLINED_SPP

namespace gpid {

    class Z3SolverInternal {
    public:
        z3::context& ctx;
        z3::solver solver;
        z3::solver csty_solver;
        Z3Storage storage;
        Z3ModelWrapper iw_mdl;

        Z3SolverInternal(z3::context& ctx)
            : ctx(ctx), solver(ctx), csty_solver(ctx), storage(ctx), iw_mdl(solver)
        { }

        inline void push() {
            solver.push();
            csty_solver.push();
        }

        inline void pop() {
            solver.pop();
            csty_solver.pop();
        }

        inline void addLiteral(Z3Literal& literal) {
            solver.add(literal.expr);
            csty_solver.add(literal.expr);
        }

        inline void storeCurrentSelection() {
            storage.insert(csty_solver.assertions(), asformula(csty_solver.assertions(), ctx), true);
        }

        inline bool wouldAcceptStorage(Z3Literal& additional) {
            csty_solver.push();
            csty_solver.add(additional.expr);
            bool res = storage.would_be_inserted(asformula(csty_solver.assertions(), ctx, true));
            csty_solver.pop();
            return res;
        }

        inline std::string hypothesisString() {
            std::stringstream result;
            result << asformula(csty_solver.assertions(), ctx);
            return result.str();
        }

    };

    inline void Z3Solver::accessLevel(uint32_t level) {
        while (level > c_level) {
            solvers->push();
            c_level++;
        }
        while (level < c_level) {
            solvers->pop();
            c_level--;
        }
    }

    inline void Z3Solver::addLiteral(Z3Literal& literal, uint32_t level) {
        accessLevel(level);
        solvers->addLiteral(literal);
    }

    inline void Z3Solver::removeLiterals(uint32_t level) {
        accessLevel(level - 1);
        accessLevel(level);
    }

    inline Z3ModelWrapper& Z3Solver::recoverModel() {
        return solvers->iw_mdl;
    }

    inline const std::string Z3Solver::hypothesisAsString() const {
        return solvers->hypothesisString();
    }

    inline void Z3Solver::printHypothesis() {
        snlog::l_warn("Not implemented yet - Z3 Solver hypothesis printer");
    }

    inline void Z3Solver::printHypothesisNegation() {
        p_implicate(std::cout, ctx, solvers->csty_solver.assertions(), true);
    }

    inline void Z3Solver::printStoredImplicates() {
        solvers->storage.print();
    }

    inline gpid::SolverTestStatus Z3Solver::testHypothesis(uint32_t level) {
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

    inline void Z3Solver::storeActive() {
        solvers->storeCurrentSelection();
    }

    inline bool Z3Solver::storageSubsumed(Z3Literal& additional, uint32_t level) {
        accessLevel(level);
        return !solvers->wouldAcceptStorage(additional);
    }

    inline bool Z3Solver::isConsequence(Z3Literal&, uint32_t level) {
        accessLevel(level);
        snlog::l_warn("Not implemented yet - Z3 consequence checker");
        return false;
    }

};

#endif
