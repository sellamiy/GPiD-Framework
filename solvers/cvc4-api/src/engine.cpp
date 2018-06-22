#ifndef GPID_CVC4_ENGINE_SRC_SPP
#define GPID_CVC4_ENGINE_SRC_SPP

using namespace gpid;

void CVC4SolverEngine::start() {
    c_level = 0;
}

void CVC4SolverEngine::setProblem(CVC4Problem& problem) {
    problem.setMode(CVC4Problem::IOMode::IO_READ);
    while (problem.hasMoreConstraints()) {
        getInterface(problemInterfaceId)._internal->solver.assertFormula(problem.nextConstraint());
    }
}

void CVC4SolverEngine::printInfos() {
    snlog::l_warn("TODO: Better Info System");
}
CVC4SolverEngine::CVC4SolverEngine() { }
CVC4SolverEngine::~CVC4SolverEngine() { }

#endif