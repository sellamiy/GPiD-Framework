#define GPID__MINISAT_SOLVER_CPP

#include <MinisatPropositionalEngine.hpp>

using namespace gpid_prop;

void MinisatSolver::start() {
    solver.eliminate(true);
    solver.verbosity = 0;
}

void MinisatSolver::setProblem(MinisatProblem& problem) {
    problem.setMode(MinisatProblem::IOMode::IO_READ);
    while (problem.hasMoreConstraints()) {
        Minisat::vec<Minisat::Lit>& ps = problem.nextConstraint();
        for (int i = 0; i < ps.size(); i++)
            while (var(ps[i]) >= solver.nVars()) solver.newVar();
        solver.addClause_(ps);
    }
}
