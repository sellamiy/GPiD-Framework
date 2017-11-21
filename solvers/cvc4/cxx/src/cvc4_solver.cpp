#define GPID__CVC4_SOLVER_CPP

#include <gpid/solvers-wrap/cvc4_engine.hpp>
#include <gpid/solvers-wrap/cvc4_solver.hpp>

using namespace gpid;

CVC4Solver::CVC4Solver()
    : solver(&em), csty_solver(&em), iw_mdl(solver)
{
    solver.setOption("incremental", true);
    solver.setOption("produce-models", true);
    solver.setLogic("QF_ALL_SUPPORTED");

    csty_solver.setOption("incremental", true);
    csty_solver.setOption("produce-models", true);
    csty_solver.setLogic("QF_ALL_SUPPORTED");
}

void CVC4Solver::start() {
    c_level = 0;
}

void CVC4Solver::setProblem(CVC4Problem& problem) {
    problem.setMode(CVC4Problem::IOMode::IO_READ);
    while (problem.hasMoreConstraints()) {
        solver.assertFormula(problem.nextConstraint());
    }
}
