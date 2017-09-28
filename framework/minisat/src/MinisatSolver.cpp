#define GPID__MINISAT_SOLVER_HPP

#include <MinisatPropositionalEngine.hpp>

using namespace gpid_prop;

void MinisatSolver::start() {
    solver.eliminate(true);
    solver.verbosity = 0;
}
