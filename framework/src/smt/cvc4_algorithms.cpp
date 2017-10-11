#define CVC4_GENERATION_INSTANCES

#include <gpid/smt/cvc4_engine.hpp>
#include <gpid/smt/cvc4_solver.hpp>
#include <gpid/algorithms/bpd_algorithm.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<CVC4Solver>;
};
