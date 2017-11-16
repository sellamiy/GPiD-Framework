#ifndef GPID_SMT_ENGINE__Z3_HPP
#define GPID_SMT_ENGINE__Z3_HPP

#include <gpid/config.hpp>
#include <gpid/core/engine.hpp>
#include <gpid/solvers-wrap/z3_context.hpp>

namespace gpid {

    struct Z3Hypothesis {
        z3::expr expr;
        Z3Hypothesis(z3::expr e) : expr(e) {}
        Z3Hypothesis(const Z3Hypothesis& e) : expr(e.expr) {}
    };
    struct Z3ModelWrapper {
        const z3::model model;
        Z3ModelWrapper(const z3::model m) : model(m) {}
        Z3ModelWrapper(const Z3ModelWrapper& mdw) : model(mdw.model) {}
        inline bool isSkippable(Z3Hypothesis& h) const {
            return model.eval(h.expr).bool_value() == Z3_lbool::Z3_L_TRUE;
        }
    };

    class Z3Problem {
    public:
        enum IOMode { IO_READ, IO_WRITE };
    private:
        IOMode mode = IOMode::IO_WRITE;
        std::vector<z3::expr> cons_data;
        uint32_t reading_pos = -1;

        z3::context& ctx;
        Z3Declarations decls;

        void initCurrentMode();
    public:
        inline Z3Problem(z3::context& ctx) : ctx(ctx), decls(ctx) {}
        inline void setMode(IOMode nmode) { mode = nmode; initCurrentMode(); }
        inline z3::context& getContext() { return ctx; }
        inline Z3Declarations& getDeclarations() { return decls; }
        void addConstraint(z3::expr cons);
        bool hasMoreConstraints();
        z3::expr nextConstraint();
    };

    class Z3Solver {
        z3::context ctx;
        z3::solver solver;
        z3::solver csty_solver;

        uint32_t c_level;

        void accessLevel(uint32_t level);
    public:
        typedef Z3Hypothesis HypothesisT;
        typedef Z3ModelWrapper ModelT;
        typedef Z3Problem ProblemT;

        void removeHypotheses(uint32_t level);
        void addHypothesis(Z3Hypothesis& hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);
        gpid::SolverTestStatus checkConsistency(uint32_t level);
        bool storageSubsumed(Z3Hypothesis& additional, uint32_t level);

        inline Z3ModelWrapper recoverModel() { return Z3ModelWrapper(solver.get_model()); }
        inline z3::context& getContext() { return ctx; }

        void printActiveNegation();
        void storeActive();

        Z3Solver();
        void setProblem(Z3Problem& problem);
        void start();
    };

    typedef HypothesesSet<Z3Solver> Z3HypothesesSet;
    typedef DecompositionEngine<Z3Solver> Z3DecompEngine;
};

#endif
