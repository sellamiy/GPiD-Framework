#ifndef GPID_SMT_ENGINE__CVC4_HPP
#define GPID_SMT_ENGINE__CVC4_HPP

#include <cvc4/cvc4.h>
#include <gpid/config.hpp>
#include <gpid/core/engine.hpp>

namespace gpid {

    // typedef /*CVC4 Content*/ CVC4Internal;
    struct CVC4Hypothesis {
    };
    struct CVC4ModelWrapper {
        inline bool isSkippable(CVC4Hypothesis& hypothesis) {
            snlog::l_warn("Not implemented yet");
            return false;
        }
    };

    class CVC4Problem {
    public:
    };

    class CVC4Solver {
        CVC4ModelWrapper iw_mdl;
    public:
        typedef CVC4Hypothesis HypothesisT;
        typedef CVC4ModelWrapper ModelT;
        typedef CVC4Problem ProblemT;

        void removeHypotheses(uint32_t level);
        void addHypothesis(CVC4Hypothesis& hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);
        bool currentlySubsumed(CVC4Hypothesis& additional, uint32_t level);

        inline CVC4ModelWrapper& recoverModel() { return iw_mdl; }

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
