#ifndef GPID_MINISAT_SOLVER_SPP
#define GPID_MINISAT_SOLVER_SPP

using namespace snlog;

namespace gpid {

    class MinisatSolverInternal {
    public:
        Minisat::SimpSolver solver;
        MinisatModelWrapper iw_mdl;
        MinisatStorage storage;
        Minisat::vec<Minisat::Lit> assumps;
        std::vector<MinisatHypothesis> loc_ass;
        Minisat::vec<int> lvl_stack;

        MinisatSolverInternal() : iw_mdl(solver.model)
        {
            solver.eliminate(true);
            solver.verbosity = 0;
        }

        inline void increaseLevel(uint32_t& c_level, uint32_t target);
        inline void decreaseLevel(uint32_t& c_level, uint32_t target);
    };

    inline void MinisatSolverInternal::increaseLevel(uint32_t& c_level, uint32_t target) {
        while (c_level < target) {
            ++c_level;
            lvl_stack.push(assumps.size());
        }
    }
    inline void MinisatSolverInternal::decreaseLevel(uint32_t& c_level, uint32_t target) {
        while (c_level > target) {
            --c_level;
            lvl_stack.pop();
            while (assumps.size() > lvl_stack.last()) {
                assumps.pop();
                loc_ass.pop_back();
            }
        }
    }

    inline void MinisatSolver::accessLevel(uint32_t level) {
        if (c_level < level) solvers->increaseLevel(c_level, level);
        else                 solvers->decreaseLevel(c_level, level);
    }

    inline void MinisatSolver::addHypothesis(MinisatHypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        solvers->loc_ass.push_back(hypothesis);
        solvers->assumps.push(hypothesis.lit);
    }

    inline void MinisatSolver::removeHypotheses(uint32_t level) {
        accessLevel(level);
    }

    inline MinisatModelWrapper& MinisatSolver::recoverModel() {
        return solvers->iw_mdl;
    }

    inline void MinisatSolver::printActiveNegation() {
        p_implicate(std::cout, solvers->assumps, true);
    }

    inline void MinisatSolver::storeActive() {
        MinisatVecWrapper<Minisat::Lit> wrp(solvers->assumps);
        solvers->storage.addSet(wrp);
    }

    inline gpid::SolverTestStatus MinisatSolver::testHypotheses(uint32_t level) {
        accessLevel(level);
        Minisat::lbool ret = solvers->solver.solveLimited(solvers->assumps);
        if      (ret == Minisat::l_True)  return gpid::SolverTestStatus::SOLVER_SAT;
        else if (ret == Minisat::l_False) return gpid::SolverTestStatus::SOLVER_UNSAT;
        else                              return gpid::SolverTestStatus::SOLVER_UNKNOWN;
    }

    inline gpid::SolverTestStatus MinisatSolver::checkConsistency(uint32_t) {
        /* For this engine, consistency is ensured by linked hypotheses */
        return SolverTestStatus::SOLVER_SAT;
    }

    inline bool MinisatSolver::storageSubsumed (MinisatHypothesis& additional, uint32_t level) {
        accessLevel(level);
        solvers->assumps.push(additional.lit);
        MinisatVecWrapper<Minisat::Lit> wrp(solvers->assumps);
        bool res = solvers->storage.subsets(wrp);
        solvers->assumps.pop();
        return res;
    }

};

#endif
