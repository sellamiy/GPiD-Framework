#define GPID_PROPOSITIONAL_PI_GENERATOR

#include <iostream>
#include <gpid/gpid.hpp>

using namespace std;
using namespace snlog;
using namespace Minisat;
using namespace gpid;

int main(int argc, char** argv) {
    CoreOptions O;
    OptionStatus status = parseOptions(O, argc, argv);
    if (status == OptionStatus::FAILURE) {
	return EXIT_FAILURE;
    } else if (status == OptionStatus::ENDED) {
	return EXIT_SUCCESS;
    }

    l_message("start propositional implicate generator...");

    MinisatSolver S;
    MinisatProblem P;

    l_message("parse problem...");
    gzFile in = gzopen(O.input.c_str(), "rb"); // TODO: Handle input errors
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
