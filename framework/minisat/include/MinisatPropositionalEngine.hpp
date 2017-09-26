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
    public:
        void addHypothesis(MinisatHypothesis hypothesis, uint32_t level);
        void removeHypotheses(uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);

        void setProblem(MinisatProblem& problem);

        void start();
    };

};

#endif
