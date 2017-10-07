#define GPID_PROPOSITIONAL_PI_GENERATOR

#include <iostream>
#include <gpid/gpid.hpp>

using namespace std;
using namespace snlog;
using namespace Minisat;
using namespace gpid;

int main(int argc, char** argv) {
    l_message("start propositional implicate generator...");
    if (argc != 2) {
        l_fatal("usage: gpid-prop <input-file>");
        return EXIT_FAILURE;
    }

    l_message("parse options...");
    CoreOptions O;
    parseOptions(O, argv);

    MinisatSolver S;
    MinisatProblem P;

    l_message("parse problem...");
    gzFile in = gzopen(argv[1], "rb"); // TODO: Handle input errors
    parse_DIMACS(in, P);
    gzclose(in);

    l_message("generate decompostition structures...");
    MinisatHypothesesSet A(2*P.getVarCpt());
    initRawSet(A);

    MinisatDecompEngine E(O.engine, S, P, A);

    l_message("generate implicates...");
    E.generateImplicates();

    l_message("complete.");
    return EXIT_SUCCESS;
}
