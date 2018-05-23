#ifndef GPID_MINISAT_SOLVER_SRC_SPP
#define GPID_MINISAT_SOLVER_SRC_SPP

using namespace gpid;

MinisatSolverInterface::MinisatSolverInterface(MinisatContextManager& ctx)
    : AbstractSolverInterface(ctx), _internal(new MinisatSolverInternal()) {}

void MinisatSolverEngine::start() {
    c_level = 0;
}

void MinisatSolverEngine::setProblem(MinisatProblem& problem) {
    problem.setMode(MinisatProblem::IOMode::IO_READ);
    for (int i = 0; i < problem.getDeclarations().nVars; i++) {
        getInterface(problemInterfaceId)._internal->solver.newVar();
        getInterface(consistencyInterfaceId)._internal->solver.newVar();
    }
    while (problem.hasMoreConstraints()) {
        Minisat::vec<Minisat::Lit>& ps = problem.nextConstraint();
        getInterface(problemInterfaceId)._internal->solver.addClause_(ps);
    }
}

void MinisatSolverEngine::printInfos() {
    snlog::l_warn("TODO: Better Info System");
}
MinisatSolverEngine::MinisatSolverEngine() { }
MinisatSolverEngine::~MinisatSolverEngine() { }

#endif
