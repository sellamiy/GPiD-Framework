#ifndef GPID_MINISAT_PARSERS_SPP
#define GPID_MINISAT_PARSERS_SPP

#include <minisat/core/Dimacs.h>

namespace gpid {

    class Wrap_MSPbl_SolverT {
        MinisatProblem& intern;
    public:
        Wrap_MSPbl_SolverT(MinisatProblem& P) : intern(P) {}

        inline void addClause_(Minisat::vec<Minisat::Lit>& ps)
        { intern.addConstraint(ps); }

        inline int nVars()   { return intern.getDeclarations().nVars; }
        inline void newVar() { intern.getDeclarations().newVar(); }
    };

    static void parse_DIMACS(std::string filename, MinisatContextManager&, MinisatProblem& P) {
        gzFile input_stream = gzopen(filename.c_str(), "rb"); // TODO: Handle input errors
        Wrap_MSPbl_SolverT wrapper(P);
        Minisat::parse_DIMACS(input_stream, wrapper);
        gzclose(input_stream);
    }

};

#endif
