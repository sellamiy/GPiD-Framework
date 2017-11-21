#ifndef GPID_SMT_ENGINE__CVC4_HPP
#define GPID_SMT_ENGINE__CVC4_HPP

#include <gpid/config.hpp>
#include <gpid/core/engine.hpp>
#include <gpid/solvers-wrap/cvc4_context.hpp>

namespace gpid {

    // typedef /*CVC4 Content*/ CVC4Internal;
    struct CVC4Hypothesis {
        CVC4::Expr expr;
        CVC4Hypothesis(CVC4::Expr e) : expr(e) {}
        CVC4Hypothesis(const CVC4Hypothesis& e) : expr(e.expr) {}
    };
    struct CVC4ModelWrapper {
        const CVC4::SmtEngine& engine;
        inline CVC4ModelWrapper(CVC4::SmtEngine& engine) : engine(engine) { }
        inline CVC4ModelWrapper(CVC4ModelWrapper& mdlw) : engine(mdlw.engine) { }
        inline bool isSkippable(CVC4Hypothesis& h) const {
            return engine.getValue(h.expr) == engine.getExprManager()->mkConst(true);
        }
    };

    class CVC4Problem {
    public:
        enum IOMode { IO_READ, IO_WRITE };
    private:
        IOMode mode = IOMode::IO_WRITE;
        std::vector<CVC4::Expr> cons_data;
        uint32_t reading_pos = -1;

        CVC4::ExprManager& em;
        CVC4Declarations decls;

        void initCurrentMode();
    public:
        CVC4Problem(CVC4::ExprManager& em) : em(em) { }

        inline void setMode(IOMode nmode) { mode = nmode; initCurrentMode(); }
        inline void collectDeclarations(CVC4::SymbolTable* table) { decls.store(table); }
        inline void collectDeclarations(CVC4::Command* cmd)       { decls.collect(cmd); }
        inline CVC4::ExprManager& getExprManager() { return em; }
        inline CVC4Declarations& getDeclarations() { return decls; }
        void addConstraint(CVC4::Expr cons);
        bool hasMoreConstraints();
        CVC4::Expr nextConstraint();
    };

    class CVC4Solver {
        CVC4::ExprManager em;
        CVC4::SmtEngine solver;
        CVC4::SmtEngine csty_solver;
        CVC4ModelWrapper iw_mdl;

        uint32_t c_level;

        void accessLevel(uint32_t level);
    public:
        typedef CVC4Hypothesis HypothesisT;
        typedef CVC4ModelWrapper ModelT;
        typedef CVC4Problem ProblemT;

        inline void printSolverInformations()
        { snlog::l_info("Interface for CVC4"); }

        void removeHypotheses(uint32_t level);
        void addHypothesis(CVC4Hypothesis& hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);
        gpid::SolverTestStatus checkConsistency(uint32_t level);
        bool storageSubsumed(CVC4Hypothesis& additional, uint32_t level);

        inline CVC4ModelWrapper& recoverModel() { return iw_mdl; }
        inline CVC4::ExprManager& getContextManager() { return em; }

        void printActiveNegation();
        void storeActive();

        CVC4Solver();
        void setProblem(CVC4Problem& problem);
        void start();
    };

    typedef HypothesesSet<CVC4Solver> CVC4HypothesesSet;
    typedef DecompositionEngine<CVC4Solver> CVC4DecompEngine;
};

#endif
