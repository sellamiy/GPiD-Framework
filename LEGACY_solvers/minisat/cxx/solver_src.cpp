#ifndef GPID_MINISAT_SOLVER_SRC_SPP
#define GPID_MINISAT_SOLVER_SRC_SPP

using namespace gpid;

void MinisatSolverEngine::setProblem(MinisatProblem& problem) {
    problem.setMode(MinisatProblem::IOMode::IO_READ);
    for (int i = 0; i < problem.getContextManager().nVars; i++) {
        getInterface(problemInterfaceId)._internal->solver.newVar();
        getInterface(consistencyInterfaceId)._internal->solver.newVar();
    }
    while (problem.hasMoreConstraints()) {
        Minisat::vec<Minisat::Lit>& ps = problem.nextConstraint();
        getInterface(problemInterfaceId)._internal->solver.addClause_(ps);
    }
}

#endif
