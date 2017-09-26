#ifndef GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP
#define GPID_PROPOSITIONAL_ENGINE__MINISAT_HPP

#include <minisat/simp/SimpSolver.h>
#include <DecompEngine.hpp>

namespace gpid_prop {

    typedef Minisat::Lit MinisatHypothesis;

    class MinisatProblem;
    class MinisatSolver;

    typedef gpid::DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver> MinisatDecompEngine;

};

#endif
