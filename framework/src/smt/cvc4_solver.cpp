#define GPID__CVC4_SOLVER_CPP

#include <gpid/smt/cvc4_engine.hpp>
#include <gpid/smt/cvc4_solver.hpp>

using namespace gpid;

CVC4Solver::CVC4Solver()
    : solver(&em)
{
    solver.setOption("incremental", true);
    solver.setOption("produce-models", true);
    solver.setLogic("QF_ALL_SUPPORTED");
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
