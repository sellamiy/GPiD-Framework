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

    CoreOptions O;

    MinisatSolver S;
    MinisatProblem P;

    gzFile in = gzopen(argv[1], "rb"); // TODO: Handle input errors
    parse_DIMACS(in, P);
    gzclose(in);

    MinisatHypothesesSet A(2*P.getVarCpt());
    initRawSet(A);

    MinisatDecompEngine E(O.engine, S, P, A);

    E.generateImplicates();

}
