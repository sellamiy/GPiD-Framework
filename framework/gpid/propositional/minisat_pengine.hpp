#ifndef GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP
#define GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP

#include <vector>
#include <minisat/simp/SimpSolver.h>
#include <gpid/core/engine.hpp>

namespace gpid {

    typedef Minisat::Lit MinisatInternal;
    struct MinisatHypothesis {
        const MinisatInternal lit;
        MinisatHypothesis(MinisatInternal d) : lit(d) {}
        MinisatHypothesis(const MinisatHypothesis& d) : lit(d.lit) {}
    };
    typedef gpid::HypothesesSet<MinisatHypothesis> MinisatHypothesesSet;
    extern void initRawSet(MinisatHypothesesSet& set);

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
        std::vector<MinisatHypothesis> loc_ass;
        Minisat::vec<int> lvl_stack;
        uint32_t c_level;

        void increaseLevel(uint32_t target);
        void decreaseLevel(uint32_t target);
        void accessLevel(uint32_t level);

    public:
        void removeHypotheses(uint32_t level) { accessLevel(level); }
        void addHypothesis(MinisatHypothesis& hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);

        inline std::vector<MinisatHypothesis>& extractActive() { return loc_ass; }

        bool isModelSkippable(MinisatHypothesis& hypothesis, uint32_t level);

        MinisatSolver();
        void setProblem(MinisatProblem& problem);
        void start();
    };
};

#endif
