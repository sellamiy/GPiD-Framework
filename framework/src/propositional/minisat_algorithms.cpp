#define MINISAT_GENERATION_INSTANCES

#include <gpid/propositional/minisat_engine.hpp>
#include <gpid/propositional/minisat_solver.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<MinisatSolver>;
};
