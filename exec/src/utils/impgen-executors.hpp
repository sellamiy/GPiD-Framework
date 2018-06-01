#ifndef GPID_EXEC__UTILS__IMPGEN_EXECUTORS_HPP
#define GPID_EXEC__UTILS__IMPGEN_EXECUTORS_HPP

#include "impgen-options.hpp"

using namespace snlog;
using namespace gpid;

enum class impgenExecutionStatus { SUCCESS, FAILURE };

template<class InterfaceT>
static inline void generate(OptionStorage& opts) {
    // TODO: Handle Errors on subcalls
    l_message("init engine...");
    ImpgenAlgorithm<AdvancedAbducibleEngine<InterfaceT>>::printInfos();

    l_message("load problem...");
    typename ImpgenAlgorithm<AdvancedAbducibleEngine<InterfaceT>>::ProblemLoaderT Loader;
    Loader.load(opts.input, opts.input_lang);
    // TODO: Loader should read problem and generate abducibles

    l_message("create decomposition engine...");
    ImpgenAlgorithm<AdvancedAbducibleEngine<InterfaceT>> Generator(Loader);

    l_message("generate implicates...");
    opts.control.time.registerTime("generation");
    Generator.execute();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of implicates generated",
                                    Generator.getGeneratedImplicatesCount());
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of nodes explored",
                                    Generator.getExploredNodesCount());
    opts.control.stats.addStatistic("Nodes skipped", "");
    for (std::pair<std::string, GPiDAlgorithm::counter_t> p : Generator.getSkippedCounts()) {
        opts.control.stats.addStatistic(p.first, p.second, 4);
    }
}

#include "sai/impgen-executors.hpp"

static inline impgenExecutionStatus generate(OptionStorage& opts) {
    return wrap_generate(opts);
}

#endif
