#define GPID__MINISAT_SOLVER_CPP

#include <gpid/propositional/minisat_pengine.hpp>
#include <gpid/propositional/minisat_wrapper.hpp>

using namespace gpid;

MinisatSolver::MinisatSolver()
    : iw_mdl(solver.model)
{
    solver.eliminate(true);
    solver.verbosity = 0;
}

void MinisatSolver::start() {
    c_level = 0;
}

void MinisatSolver::setProblem(MinisatProblem& problem) {
    problem.setMode(MinisatProblem::IOMode::IO_READ);
    for (int i = 0; i < problem.getVarCpt(); i++)
        solver.newVar();
    while (problem.hasMoreConstraints()) {
        Minisat::vec<Minisat::Lit>& ps = problem.nextConstraint();
        solver.addClause_(ps);
    }
}
