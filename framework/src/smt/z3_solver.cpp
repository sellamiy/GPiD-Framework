#define GPID__Z3_SOLVER_CPP

#include <gpid/smt/z3_engine.hpp>
#include <gpid/smt/z3_solver.hpp>

using namespace gpid;

Z3Solver::Z3Solver()
    : solver(ctx), csty_solver(ctx)
{
}

void Z3Solver::start() {
    c_level = 0;
}

void Z3Solver::setProblem(Z3Problem& problem) {
    problem.setMode(Z3Problem::IOMode::IO_READ);
    while (problem.hasMoreConstraints()) {
        solver.add(problem.nextConstraint());
    }
}
