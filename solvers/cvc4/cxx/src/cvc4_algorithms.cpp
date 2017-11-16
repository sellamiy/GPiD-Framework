#define CVC4_GENERATION_INSTANCES

#include <gpid/solvers-wrap/cvc4_engine.hpp>
#include <gpid/solvers-wrap/cvc4_solver.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<CVC4Solver>;
};
