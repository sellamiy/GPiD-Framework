#define TRUE_SOLVER_GENERATION_INSTANCES

#include <gpid/core/engine.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<TrueSolver>;
};
