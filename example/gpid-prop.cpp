#define GPID_PROPOSITIONAL_PI_GENERATOR

#include <iostream>
#include <MinisatPropositionalEngine.hpp>

using namespace std;
using namespace Minisat;
using namespace gpid_prop;

int main(int argc, char** argv) {
    if (argc != 2) {
        cout << "usage: gpid-prop <input-file>" << endl;
    }

    MinisatSolver S;
    MinisatProblem P;

    MinisatHypothesesSet A;

    MinisatDecompEngine E(S, P, A);

}
