#ifndef GPID_EXEC__UTILS__GTS_EXECUTORS_HPP
#define GPID_EXEC__UTILS__GTS_EXECUTORS_HPP

#include "gts-options.hpp"

using namespace snlog;
using namespace gpid;

enum gtsExecutionStatus { GTS_SUCCESS, GTS_FAILURE };

template<class Solver>
static inline void generate(OptionStorage& opts) {
    // TODO: Handle Errors on subcalls
    l_message("init engine...");
    Solver S;
    typename Solver::ProblemT P(S.getContextManager());
    S.printInfos();

    l_message("parse problem...");
    parse_file(opts.input, S.getContextManager(), P, opts.input_lang);

    l_message("generate abducibles...");
    SkipperController SkCtrl(opts);
    LiteralsEngine<Solver> A(S, SkCtrl, countAbducibles(opts.abducibles, P));
    generateAbducibles(opts.abducibles, S.getContextManager(), P.getDeclarations(), A);

    l_message("create decomposition engine...");
    DecompositionEngine<Solver> E(opts.engine, S, P, A);

    l_message("generate implicates...");
    opts.control.time.registerTime("generation");
    E.generateImplicates();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of implicates generated", E.getGeneratedImplicatesCount());
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of nodes explored", E.getExploredNodesCount());
    opts.control.stats.addStatistic("Nodes skipped", "");
    for (std::pair<std::string, uint64_t> p : A.getSkippedCounts()) {
        opts.control.stats.addStatistic(p.first, p.second, 4);
    }
}

#include <gpid/solver-snippets/gts-executors.hpp>

static inline gtsExecutionStatus generate(OptionStorage& opts) {
    return wrap_generate(opts);
}

#endif
