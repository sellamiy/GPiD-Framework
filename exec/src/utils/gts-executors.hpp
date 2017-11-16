#ifndef _INCL_EX_EXECUTORS_PARSER_
#define _INCL_EX_EXECUTORS_PARSER_

#ifdef SINGLE_SOLVER_ONLY
#ifdef SINGLE_SOLVER_TRUESOLVER
#include <gpid/gpid.hpp>
#elif SINGLE_SOLVER_MINISAT
#include <gpid/solvers/minisat.hpp>
#elif SINGLE_SOLVER_CVC4
#include <gpid/solvers/cvc4.hpp>
#elif SINGLE_SOLVER_Z3
#include <gpid/solvers/z3.hpp>
#else
#error Unsupported Single Solver
#endif
#else
#include <gpid/solvers/all.hpp>
#define SINGLE_SOLVER_TRUESOLVER
#define SINGLE_SOLVER_MINISAT
#define SINGLE_SOLVER_CVC4
#define SINGLE_SOLVER_Z3
#endif
#include "gts-options.hpp"

using namespace snlog;
using namespace gpid;

#ifdef SINGLE_SOLVER_TRUESOLVER
static inline void generate_true_solver(OptionStorage& opts) {
    l_info("True Solver -- The Only True Solver.");
    TrueSolver S;
    TrueSolver::ProblemT P;
    l_message("generate decompostition structures...");
    SkipperController SkCtrl(opts);
    HypothesesSet<TrueSolver> A(S, SkCtrl, 1);
    DecompositionEngine<TrueSolver> E(opts.engine, S, P, A);
    l_message("generate implicates...");
    opts.control.time.registerTime("generation");
    E.generateImplicates();
    opts.control.time.registerTime("generation-end");
}
/*
static inline void generate_true_solver(OptionStorage&) {
    l_internal("Got access to unconfigured interface generator");
}
*/
#endif

#ifdef SINGLE_SOLVER_MINISAT
static inline void generate_minisat(OptionStorage& opts) {
    l_message("start minisat engine...");
    MinisatSolver S;
    MinisatProblem P;

    l_message("parse problem...");
    parse_file(opts.input, P, opts.input_lang);

    l_message("generate abducibles...");
    SkipperController SkCtrl(opts);
    MinisatHypothesesSet A(S, SkCtrl, countAbducibles(opts.abducibles, P));
    generateAbducibles(opts.abducibles, A, P.getVarCpt()); // TODO: Handle errors

    l_message("create decomposition engine...");
    MinisatDecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    opts.control.time.registerTime("generation");
    E.generateImplicates();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of implicates generated", E.getGeneratedImplicatesCount());
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of nodes explored", E.getExploredNodesCount());
    opts.control.stats.addStatistic("Number of nodes skipped", "");
    opts.control.stats.addStatistic("Inconsistency", E.getInconsistentNodesSkippedCount(), 4);
}
#endif

#ifdef SINGLE_SOLVER_CVC4
static inline void generate_cvc4(OptionStorage& opts) {
    l_message("init cvc4 engine...");
    CVC4Solver S;
    CVC4Problem P;

    l_message("parse problem...");
    parse_file(opts.input, S.getExprManager(), P, opts.input_lang); // TODO: Handle errors

    l_message("generate abducibles...");
    SkipperController SkCtrl(opts);
    CVC4HypothesesSet A(S, SkCtrl, countAbducibles(opts.abducibles, P));
    generateAbducibles(opts.abducibles, S.getExprManager(), P.getDeclarations(), A); // TODO: Handle errors

    l_message("create decomposition engine...");
    CVC4DecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    opts.control.time.registerTime("generation");
    E.generateImplicates();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of implicates generated", E.getGeneratedImplicatesCount());
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of nodes explored", E.getExploredNodesCount());
    opts.control.stats.addStatistic("Number of nodes skipped", "");
    opts.control.stats.addStatistic("Inconsistency", E.getInconsistentNodesSkippedCount(), 4);
}
#endif

#ifdef SINGLE_SOLVER_Z3
static inline void generate_z3(OptionStorage& opts) {
    l_message("init z3 engine...");
    Z3Solver S;
    Z3Problem P(S.getContext());

    l_message("parse problem...");
    parse_file(opts.input, P, opts.input_lang); // TODO: Handle errors

    l_message("generate abducibles...");
    SkipperController SkCtrl(opts);
    Z3HypothesesSet A(S, SkCtrl, countAbducibles(opts.abducibles, P));
    generateAbducibles(opts.abducibles, S.getContext(), P.getDeclarations(), A); // TODO: Handle errors

    l_message("create decomposition engine...");
    Z3DecompEngine E(opts.engine, S, P, A);

    l_message("generate implicates...");
    opts.control.time.registerTime("generation");
    E.generateImplicates();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of implicates generated", E.getGeneratedImplicatesCount());
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of nodes explored", E.getExploredNodesCount());
    opts.control.stats.addStatistic("Number of nodes skipped", "");
    opts.control.stats.addStatistic("Inconsistency", E.getInconsistentNodesSkippedCount(), 4);
}
#endif

#ifdef SINGLE_SOLVER_ONLY
static inline void generate(OptionStorage& opts) {
#if SINGLE_SOLVER_TRUESOLVER
    generate_true_solver(opts);
#elif SINGLE_SOLVER_MINISAT
    generate_minisat(opts);
#elif SINGLE_SOLVER_CVC4
    generate_cvc4(opts);
#elif SINGLE_SOLVER_Z3
    generate_z3(opts);
#endif
}
#endif

#endif
