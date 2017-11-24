#ifndef GPID_CVC4_SOLVER_SRC_SPP
#define GPID_CVC4_SOLVER_SRC_SPP

gpid::CVC4Solver::CVC4Solver() : solvers(new Internal(&ctx)) { }

gpid::CVC4Solver::~CVC4Solver() { }

void gpid::CVC4Solver::start() {
    c_level = 0;
}

void gpid::CVC4Solver::setProblem(CVC4Problem& problem) {
    problem.setMode(CVC4Problem::IOMode::IO_READ);
    while (problem.hasMoreConstraints()) {
        solvers->solver.assertFormula(problem.nextConstraint());
    }
}

#endif
