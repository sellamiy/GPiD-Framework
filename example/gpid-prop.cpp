#define GPID_PROPOSITIONAL_PI_GENERATOR

#include <iostream>
#include <gpid/gpid.hpp>

using namespace std;
using namespace Minisat;
using namespace gpid;

int main(int argc, char** argv) {
    if (argc != 2) {
        cout << "usage: gpid-prop <input-file>" << endl;
    }

    MinisatSolver S;
    MinisatProblem P;

    gzFile in = gzopen(argv[1], "rb"); // TODO: Handle input errors
    parse_DIMACS(in, P);
    gzclose(in);

    MinisatHypothesesSet A(2*P.getVarCpt());

    // TODO: Read problem from file and store clauses in P
    // TODO: Read problem from file and store abducoble hypotheses in A

    MinisatDecompEngine E(S, P, A);

    E.generateImplicates();

}
