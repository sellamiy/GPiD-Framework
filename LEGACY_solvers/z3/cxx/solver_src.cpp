#ifndef GPID_Z3_SOLVER_SRC_SPP
#define GPID_Z3_SOLVER_SRC_SPP

#include <fstream>

using namespace gpid;

Z3SolverInterface::Z3SolverInterface(z3::context& ctx)
    : AbstractSolverInterface(ctx), _internal(new Z3SolverInternal(ctx)) { }

void Z3SolverEngine::start() {
    c_level = 0;
}

void Z3SolverEngine::setProblem(Z3Problem& problem) {
    problem.setMode(Z3Problem::IOMode::IO_READ);
    while (problem.hasMoreConstraints()) {
        getInterface(problemInterfaceId)._internal->solver.add(problem.nextConstraint());
    }
}

void Z3SolverEngine::printInfos() {
    snlog::l_warn("TODO: Better Info System");
}
Z3SolverEngine::Z3SolverEngine() { }
Z3SolverEngine::~Z3SolverEngine() { }

#endif
