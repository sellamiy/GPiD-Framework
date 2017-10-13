#define Z3_GENERATION_INSTANCES

#include <gpid/smt/z3_engine.hpp>
#include <gpid/smt/z3_solver.hpp>
#include <gpid/algorithms/bpd_algorithm.hpp>
#include <gpid/algorithms/pid_algorithm.hpp>

namespace gpid {
    template class DecompositionEngine<Z3Solver>;
};
