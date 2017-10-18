#ifndef _INCL_EX_EXECUTORS_PARSER_
#define _INCL_EX_EXECUTORS_PARSER_

#include <gpid/gpid.hpp>
#include "gts-options.hpp"

using namespace snlog;
using namespace gpid;

#ifdef TRUE_SOLVER_INTERFACE
static inline void generate_true_solver(OptionStorage& opts) {
    l_info("True Solver -- The Only True Solver.");
    TrueSolver S;
    TrueSolver::ProblemT P;
    l_message("generate decompostition structures...");
    HypothesesSet<TrueSolver> A(1);
    DecompositionEngine<TrueSolver> E(opts.engine, S, P, A);
    l_message("generate implicates...");
    E.generateImplicates();
    l_message("print generation statistics...");
    E.printStatistics();
}
#else
static inline void generate_true_solver(OptionStorage&) {
    l_internal("Got access to unconfigured interface generator");
}
#endif

#ifdef MINISAT_SOLVER_INTERFACE
static inline void generate_minisat(OptionStorage& opts) {
    l_message("start minisat engine...");
    MinisatSolver S;
    MinisatProblem P;

    l_message("parse problem...");
    gzFile in = gzopen(opts.input.c_str(), "rb"); // TODO: Handle input errors
    parse_DIMACS(in, P);
    gzclose(in);

    l_message("generate abducibles...");
    MinisatHypothesesSet A(countAbducibles(opts.abducibles, P));
    generateAbducibles(opts.abducibles, A, P.getVarCpt()); // TODO: Handle errors

    l_message("create decomposition engine...");
    MinisatDecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    E.generateImplicates();

    l_message("print generation statistics...");
    E.printStatistics();
}
#else
static inline void generate_minisat(OptionStorage&) {
    l_internal("Got access to unconfigured interface generator");
}
#endif

#ifdef CVC4_SOLVER_INTERFACE
static inline void generate_cvc4(OptionStorage& opts) {
    l_message("init cvc4 engine...");
    CVC4Solver S;
    CVC4Problem P;

    l_message("parse problem...");
    parse_Cvc(opts.input, S.getExprManager(), P); // TODO: Handle errors

    l_message("generate abducibles...");
    CVC4HypothesesSet A(countAbducibles(opts.abducibles, P));
    generateAbducibles(opts.abducibles, S.getExprManager(), P.getDeclarations(), A); // TODO: Handle errors

    l_message("create decomposition engine...");
    CVC4DecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    E.generateImplicates();

    l_message("print generation statistics...");
    E.printStatistics();
}
#else
static inline void generate_cvc4(OptionStorage&) {
    l_internal("Got access to unconfigured interface generator");
}
#endif

#ifdef Z3_SOLVER_INTERFACE
static inline void generate_z3(OptionStorage& opts) {
    l_message("init z3 engine...");
    Z3Solver S;
    Z3Problem P;

    l_message("parse problem...");
    parse_Z(opts.input, S.getContext(), P); // TODO: Handle errors

    l_message("generate abducibles...");
    Z3HypothesesSet A(countAbducibles(opts.abducibles, P));
    generateAbducibles(opts.abducibles, S.getContext(), P.getDeclarations(), A); // TODO: Handle errors

    l_message("create decomposition engine...");
    Z3DecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    E.generateImplicates();

    l_message("print generation statistics...");
    E.printStatistics();
}
#else
static inline void generate_z3(OptionStorage&) {
    l_internal("Got access to unconfigured interface generator");
}
#endif

#endif
