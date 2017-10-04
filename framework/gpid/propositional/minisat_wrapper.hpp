#ifndef GPID_PROPOSITIONAL_SOLVER__MINISAT_DETAILS_HPP
#define GPID_PROPOSITIONAL_SOLVER__MINISAT_DETAILS_HPP

#include <gpid/propositional/minisat_pengine.hpp>

namespace gpid {

    inline void MinisatSolver::increaseLevel(uint32_t target) {
        while (c_level < target) {
            ++c_level;
            lvl_stack.push(assumps.size());
        }
    }
    inline void MinisatSolver::decreaseLevel(uint32_t target) {
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
        if (c_level < level) increaseLevel(level);
        else decreaseLevel(level);
    }

    inline void MinisatSolver::addHypothesis(MinisatHypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
        loc_ass.push_back(hypothesis);
        assumps.push(hypothesis.lit);
    }

    inline gpid::SolverTestStatus MinisatSolver::testHypotheses(uint32_t level) {
        accessLevel(level);
        Minisat::lbool ret = solver.solveLimited(assumps);
        if      (ret == Minisat::l_True)  return gpid::SolverTestStatus::SOLVER_SAT;
        else if (ret == Minisat::l_False) return gpid::SolverTestStatus::SOLVER_UNSAT;
        else                              return gpid::SolverTestStatus::SOLVER_UNKNOWN;
    }

};

#endif
