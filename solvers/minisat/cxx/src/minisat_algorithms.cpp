#define MINISAT_GENERATION_INSTANCES

#include <gpid/solvers-wrap/minisat_engine.hpp>
#include <gpid/solvers-wrap/minisat_solver.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<MinisatSolver>;
};
