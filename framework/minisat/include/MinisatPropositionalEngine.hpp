#ifndef GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP
#define GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP

#include <minisat/simp/SimpSolver.h>
#include <DecompEngine.hpp>

namespace gpid_prop {

    typedef Minisat::Lit MinisatInternal;
    struct MinisatHypothesis {
        const MinisatInternal lit;
        MinisatHypothesis(MinisatInternal d) : lit(d) {}
        MinisatHypothesis(MinisatHypothesis& d) : lit(d.lit) {}
    };
    typedef gpid::HypothesesSet<MinisatHypothesis> MinisatHypothesesSet;

    class MinisatProblem;
    class MinisatSolver;

    typedef gpid::DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver> MinisatDecompEngine;

    class MinisatProblem {

    };

    class MinisatSolver {
        Minisat::SimpSolver solver;
        Minisat::vec<Minisat::Lit> assumps;
        Minisat::vec<uint32_t> lvl_stack;
        uint32_t c_level;

        inline void increaseLevel(uint32_t target);
        inline void decreaseLevel(uint32_t target);
        inline void accessLevel(uint32_t level) {
            if (c_level < level) increaseLevel(level);
            else decreaseLevel(level);
        }
    public:
        inline void removeHypotheses(uint32_t level) { accessLevel(level); }
        inline void addHypothesis(MinisatHypothesis hypothesis, uint32_t level) {
            accessLevel(level);
            assumps.push(hypothesis.lit);
        }

        inline gpid::SolverTestStatus testHypotheses(uint32_t level) {
            accessLevel(level);
            Minisat::lbool ret = solver.solveLimited(assumps);
            if      (ret == Minisat::l_True)  return gpid::SolverTestStatus::SOLVER_SAT;
            else if (ret == Minisat::l_False) return gpid::SolverTestStatus::SOLVER_UNSAT;
            else                              return gpid::SolverTestStatus::SOLVER_UNKNOWN;
        }

        void setProblem(MinisatProblem& problem);

        void start();
    };

    inline void MinisatSolver::increaseLevel(uint32_t target) {
        while (c_level < target) {
            ++c_level;
            lvl_stack.push(assumps.size());
        }
    }
    inline void MinisatSolver::decreaseLevel(uint32_t target) {
        while (c_level > target) {
            --c_level;
            while (assumps.size() > lvl_stack.last()) assumps.pop();
            lvl_stack.pop();
        }
    }

};

#endif
