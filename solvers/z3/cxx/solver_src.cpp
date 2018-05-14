#ifndef GPID_Z3_SOLVER_SRC_SPP
#define GPID_Z3_SOLVER_SRC_SPP

#include <fstream>

using namespace gpid;

Z3Solver::Z3Solver()
    : solvers(new Internal(ctx))
{ }

Z3Solver::~Z3Solver() { }

void Z3Solver::start() {
    c_level = 0;
}

void Z3Solver::setProblem(Z3Problem& problem) {
    problem.setMode(Z3Problem::IOMode::IO_READ);
    while (problem.hasMoreConstraints()) {
        solvers->solver.add(problem.nextConstraint());
    }
}

void Z3Solver::exportStoredImplicates() {
    std::ofstream target("z3storage.pcc-auto.dot");
    solvers->storage.asGraph(target);
}

#endif
