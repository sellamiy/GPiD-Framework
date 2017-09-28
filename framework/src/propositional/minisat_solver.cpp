#define GPID__MINISAT_SOLVER_CPP

#include <gpid/propositional/pengine_minisat.hpp>

using namespace gpid;

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
