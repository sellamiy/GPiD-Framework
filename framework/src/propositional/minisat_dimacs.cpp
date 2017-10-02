#define MINISAT_DIMACS_PARSING

#include <gpid/propositional/minisat_inputs.hpp>
#include <minisat/core/Dimacs.h>

namespace gpid {

    class Wrap_MSPbl_SolverT {
        MinisatProblem& intern;
    public:
        Wrap_MSPbl_SolverT(MinisatProblem& P) : intern(P) {}

        inline void addClause_(Minisat::vec<Minisat::Lit>& ps)
        { intern.addConstraint(ps); }

        inline int nVars()   { return intern.getVarCpt(); }
        inline void newVar() { intern.newVar(); }
    };

    extern void parse_DIMACS(gzFile input_stream, MinisatProblem& P, bool strictp) {
        Wrap_MSPbl_SolverT wrapper(P);
        Minisat::parse_DIMACS(input_stream, wrapper, strictp);
    }

};
