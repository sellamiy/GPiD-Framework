#ifndef GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP
#define GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP

#include <minisat/simp/SimpSolver.h>
#include <gpid/core/engine.hpp>

namespace gpid {

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
    public:
        enum IOMode { IO_READ, IO_WRITE };
    private:
        int var_cpt = 0;
        IOMode mode = IOMode::IO_WRITE;

        Minisat::vec<Minisat::Lit> cons_data;
        Minisat::vec<int> cons_sep;

        Minisat::vec<int> read_session_seps;
        Minisat::vec<Minisat::Lit> read_session_data;
        Minisat::vec<Minisat::Lit> read_local_data;

        void initCurrentMode();
    public:
        inline int getVarCpt() { return var_cpt; }
        inline void newVar() { ++var_cpt; }
        inline void setMode(IOMode nmode) { mode = nmode; initCurrentMode(); }

        void addConstraint(Minisat::vec<Minisat::Lit>& ps);
        bool hasMoreConstraints();
        Minisat::vec<Minisat::Lit>& nextConstraint();
    };

    class MinisatSolver {
        Minisat::SimpSolver solver;
        Minisat::vec<Minisat::Lit> assumps;
        Minisat::vec<uint32_t> lvl_stack;
        uint32_t c_level;

        inline void increaseLevel(uint32_t target);
        inline void decreaseLevel(uint32_t target);
        inline void accessLevel(uint32_t level);

    public:
        inline void removeHypotheses(uint32_t level) { accessLevel(level); }
        inline void addHypothesis(MinisatHypothesis& hypothesis, uint32_t level);
        inline gpid::SolverTestStatus testHypotheses(uint32_t level);

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

    inline void MinisatSolver::accessLevel(uint32_t level) {
        if (c_level < level) increaseLevel(level);
        else decreaseLevel(level);
    }

    inline void MinisatSolver::addHypothesis(MinisatHypothesis& hypothesis, uint32_t level) {
        accessLevel(level);
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
