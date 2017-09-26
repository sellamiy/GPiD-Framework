#ifndef GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP
#define GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP

#include <minisat/simp/SimpSolver.h>
#include <DecompEngine.hpp>

namespace gpid_prop {

    typedef Minisat::Lit MinisatHypothesis;
    typedef gpid::HypothesesSet<MinisatHypothesis> MinisatHypothesesSet;

    class MinisatProblem;
    class MinisatSolver;

    typedef gpid::DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver> MinisatDecompEngine;

    class MinisatProblem {

    };

    class MinisatSolver {
    public:
        void addHypothesis(MinisatHypothesis hypothesis, uint32_t level);
        gpid::SolverTestStatus testHypotheses(uint32_t level);
    };

};

#endif
