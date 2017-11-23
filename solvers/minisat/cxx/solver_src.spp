#ifndef GPID_MINISAT_SOLVER_SRC_SPP
#define GPID_MINISAT_SOLVER_SRC_SPP

using namespace gpid;

MinisatSolver::MinisatSolver() : solvers(new MinisatSolverInternal()) { }

MinisatSolver::~MinisatSolver() { }

void MinisatSolver::start() {
    c_level = 0;
}

void MinisatSolver::setProblem(MinisatProblem& problem) {
    problem.setMode(MinisatProblem::IOMode::IO_READ);
    for (int i = 0; i < problem.getDeclarations().nVars; i++)
        solvers->solver.newVar();
    while (problem.hasMoreConstraints()) {
        Minisat::vec<Minisat::Lit>& ps = problem.nextConstraint();
        solvers->solver.addClause_(ps);
    }
}

#endif
