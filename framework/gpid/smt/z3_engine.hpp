#ifndef GPID_SMT_ENGINE__Z3_HPP
#define GPID_SMT_ENGINE__Z3_HPP

#include <gpid/config.hpp>
#include <gpid/core/engine.hpp>
#include <gpid/smt/z3_context.hpp>

namespace gpid {

    struct Z3Hypothesis {
        z3::expr expr;
        Z3Hypothesis(z3::expr e) : expr(e) {}
        Z3Hypothesis(const Z3Hypothesis& e) : expr(e.expr) {}
    };
    struct Z3ModelWrapper {
        inline bool isSkippable(Z3Hypothesis& hypothesis) {
            snlog::l_warn("Not implemented yet - Z3 model wrapper skipper");
            return false;
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
        Z3ModelWrapper iw_mdl;

        // TODO: Fix. This is only required for printing. Not efficient -> needs improvement
        std::vector<Z3Hypothesis> hyp_loc_mem;

        uint32_t c_level;

        void accessLevel(uint32_t level);
    public:
        typedef Z3Hypothesis HypothesisT;
        typedef Z3ModelWrapper ModelT;
        typedef Z3Problem ProblemT;

        inline void removeHypotheses(uint32_t level) { accessLevel(level); }
        void addHypothesis(Z3Hypothesis& hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);
        bool currentlySubsumed(Z3Hypothesis& additional, uint32_t level);

        inline Z3ModelWrapper& recoverModel() { return iw_mdl; }
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
