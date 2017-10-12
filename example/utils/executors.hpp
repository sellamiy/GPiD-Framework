#ifndef _INCL_EX_EXECUTORS_PARSER_
#define _INCL_EX_EXECUTORS_PARSER_

#include <gpid/gpid.hpp>
#include "options_parser.hpp"

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
static inline void generate_true_solver(OptionStorage& opts __attribute__((unused))) {
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

    l_message("generate decompostition structures...");
    MinisatHypothesesSet A(2*P.getVarCpt());
    initRawSet(A);

    MinisatDecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    E.generateImplicates();

    l_message("print generation statistics...");
    E.printStatistics();
}
#else
static inline void generate_minisat(OptionStorage& opts __attribute__((unused))) {
    l_internal("Got access to unconfigured interface generator");
}
#endif

#ifdef CVC4_SOLVER_INTERFACE
static inline void generate_cvc4(OptionStorage& opts) {
    l_message("init cvc4 engine...");
    CVC4Solver S;
    CVC4Problem P;

    l_message("parse problem...");
    parse_Cvc(opts.input, S.getExprManager(), P);

    l_message("generate decomposition structures...");
    l_warn("FIXME: cvc4 decomposition structures");
    CVC4HypothesesSet A(1/* TODO: Correct size */);
    initRawSet(S.getExprManager(), A);

    CVC4DecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    E.generateImplicates();

    l_message("print generation statistics...");
    E.printStatistics();
}
#else
static inline void generate_cvc4(OptionStorage& opts __attribute__((unused))) {
    l_internal("Got access to unconfigured interface generator");
}
#endif

#endif
