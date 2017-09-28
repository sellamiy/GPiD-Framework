#define MINISAT_GENERATION_INSTANCES

#include <gpid/propositional/pengine_minisat.hpp>
#include <gpid/algorithms/bpd_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<MinisatHypothesis, MinisatProblem, MinisatSolver>;
};
