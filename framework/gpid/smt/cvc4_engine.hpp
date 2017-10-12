#ifndef GPID_SMT_ENGINE__CVC4_HPP
#define GPID_SMT_ENGINE__CVC4_HPP

#include <vector>
#include <cvc4/cvc4.h>
#include <gpid/config.hpp>
#include <gpid/core/engine.hpp>

namespace gpid {

    // typedef /*CVC4 Content*/ CVC4Internal;
    struct CVC4Hypothesis {
        CVC4::Expr& expr;
        CVC4Hypothesis(CVC4::Expr& e) : expr(e) {}
        CVC4Hypothesis(CVC4Hypothesis& e) : expr(e.expr) {}
    };
    struct CVC4ModelWrapper {
        inline bool isSkippable(CVC4Hypothesis& hypothesis) {
            snlog::l_warn("Not implemented yet");
            return false;
        }
    };

    class CVC4Problem {
    public:
        enum IOMode { IO_READ, IO_WRITE };
    private:
        IOMode mode = IOMode::IO_WRITE;
        std::vector<CVC4::Expr> cons_data;
        uint32_t reading_pos = -1;

        void initCurrentMode();
    public:
        inline void setMode(IOMode nmode) { mode = nmode; initCurrentMode(); }
        void addConstraint(CVC4::Expr cons);
        bool hasMoreConstraints();
        CVC4::Expr& nextConstraint();
    };

    class CVC4Solver {
        CVC4::ExprManager em;
        CVC4::SmtEngine solver;
        CVC4ModelWrapper iw_mdl;

        uint32_t c_level;

        void accessLevel(uint32_t level);
    public:
        typedef CVC4Hypothesis HypothesisT;
        typedef CVC4ModelWrapper ModelT;
        typedef CVC4Problem ProblemT;

        inline void removeHypotheses(uint32_t level) { accessLevel(level); }
        void addHypothesis(CVC4Hypothesis& hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);
        bool currentlySubsumed(CVC4Hypothesis& additional, uint32_t level);

        inline CVC4ModelWrapper& recoverModel() { return iw_mdl; }
        inline CVC4::ExprManager& getExprManager() { return em; }

        void printActiveNegation();
        void storeActive();

        CVC4Solver();
        void setProblem(CVC4Problem& problem);
        void start();
    };

    typedef HypothesesSet<CVC4Solver> CVC4HypothesesSet;
    typedef DecompositionEngine<CVC4Solver> CVC4DecompEngine;
    extern void initRawSet(CVC4HypothesesSet& set);
};

#endif
