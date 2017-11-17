#ifndef GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP
#define GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP

#include <vector>
#include <ugly/ugly.hpp>
#include <minisat/simp/SimpSolver.h>
#include <gpid/config.hpp>
#include <gpid/core/engine.hpp>
#include <gpid/solvers-wrap/minisat_wrappers.hpp>

namespace gpid {

    typedef Minisat::Lit MinisatInternal;
    struct MinisatHypothesis {
        const MinisatInternal lit;
        MinisatHypothesis(MinisatInternal d) : lit(d) {}
        MinisatHypothesis(const MinisatHypothesis& d) : lit(d.lit) {}
    };
    struct MinisatModelWrapper {
        const Minisat::vec<Minisat::lbool>& model;
        MinisatModelWrapper(Minisat::vec<Minisat::lbool>& m) : model(m) {}
        inline bool isSkippable(MinisatHypothesis& hypothesis) const {
            return model[Minisat::var(hypothesis.lit)] == (sign(hypothesis.lit) ? Minisat::l_False : Minisat::l_True);
        }
    };

    struct MinisatContext { };
    struct MinisatDeclarations { int nVars = 0; };

    class MinisatProblem {
    public:
        enum IOMode { IO_READ, IO_WRITE };
    private:
        MinisatDeclarations decls;
        IOMode mode = IOMode::IO_WRITE;

        Minisat::vec<Minisat::Lit> cons_data;
        Minisat::vec<int> cons_sep;

        Minisat::vec<int> read_session_seps;
        Minisat::vec<Minisat::Lit> read_session_data;
        Minisat::vec<Minisat::Lit> read_local_data;

        void initCurrentMode();
    public:
        MinisatProblem(MinisatContext&) { }

        inline MinisatDeclarations& getDeclarations() { return decls; }

        inline int getVarCpt() { return decls.nVars; }
        inline void newVar() { ++decls.nVars; }
        inline void setMode(IOMode nmode) { mode = nmode; initCurrentMode(); }

        void addConstraint(Minisat::vec<Minisat::Lit>& ps);
        bool hasMoreConstraints();
        Minisat::vec<Minisat::Lit>& nextConstraint();
    };

    typedef ugly::SetOfSets<Minisat::Lit, MinisatVecWrapper<Minisat::Lit> > MinisatStorage;

    class MinisatSolver {
        Minisat::SimpSolver solver;
        MinisatModelWrapper iw_mdl;
        MinisatStorage storage;
        Minisat::vec<Minisat::Lit> assumps;
        std::vector<MinisatHypothesis> loc_ass;
        Minisat::vec<int> lvl_stack;
        uint32_t c_level;

        MinisatContext ctx;

        void increaseLevel(uint32_t target);
        void decreaseLevel(uint32_t target);
        void accessLevel(uint32_t level);

    public:
        typedef MinisatHypothesis HypothesisT;
        typedef MinisatProblem ProblemT;
        typedef MinisatModelWrapper ModelT;
        typedef MinisatStorage StorageT;

        inline void printSolverInformations()
        { snlog::l_info("Interface for Minisat"); }

        void removeHypotheses(uint32_t level) { accessLevel(level); }
        void addHypothesis(MinisatHypothesis& hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);
        inline gpid::SolverTestStatus checkConsistency(uint32_t)
        /* For this engine, consistency is ensured by linked hypotheses */
        { return SolverTestStatus::SOLVER_SAT; }
        bool storageSubsumed(MinisatHypothesis& additional, uint32_t level);

        inline std::vector<MinisatHypothesis>& extractActive() { return loc_ass; }
        inline MinisatModelWrapper& recoverModel() { return iw_mdl; }
        inline MinisatStorage& getStorage() { return storage; }
        inline MinisatContext& getContextManager() { return ctx; }

        void printActiveNegation();
        void storeActive();

        MinisatSolver();
        void setProblem(MinisatProblem& problem);
        void start();
    };

    typedef HypothesesSet<MinisatSolver> MinisatHypothesesSet;
    typedef DecompositionEngine<MinisatSolver> MinisatDecompEngine;
};

#endif
