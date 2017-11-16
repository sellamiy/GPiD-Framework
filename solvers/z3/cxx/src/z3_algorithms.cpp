#define Z3_GENERATION_INSTANCES

#include <gpid/solvers-wrap/z3_engine.hpp>
#include <gpid/solvers-wrap/z3_solver.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<Z3Solver>;
};
