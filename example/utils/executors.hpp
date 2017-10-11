#ifndef _INCL_EX_EXECUTORS_PARSER_
#define _INCL_EX_EXECUTORS_PARSER_

#include <gpid/gpid.hpp>
#include "options_parser.hpp"

using namespace snlog;
using namespace gpid;

#ifdef TRUE_SOLVER_INTERFACE
static inline void generate_true_solver(OptionStorage& opts __attribute__((unused))) {
    l_message("True Solver -- The Only True Solver.");
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
}
#else
static inline void generate_minisat(OptionStorage& opts __attribute__((unused))) {
    l_internal("Got access to unconfigured interface generator");
}
#endif

#endif
