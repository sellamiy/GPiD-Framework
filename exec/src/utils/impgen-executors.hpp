#ifndef GPID_EXEC__UTILS__IMPGEN_EXECUTORS_HPP
#define GPID_EXEC__UTILS__IMPGEN_EXECUTORS_HPP

#include "impgen-options.hpp"

using namespace snlog;
using namespace gpid;

enum class impgenExecutionStatus { SUCCESS, FAILURE };

template<class EngineT, class LiteralGeneratorT>
static inline void generate_upae_x(OptionStorage& opts) {
    // TODO: Handle Errors on subcalls
    l_message("init engine...");
    ImpgenAlgorithm<EngineT, LiteralGeneratorT>::printInfos();

    l_message("load problem...");
    typename ImpgenAlgorithm<EngineT, LiteralGeneratorT>::
        ProblemLoaderT Loader;
    Loader.load(opts.input, opts.input_lang);

    l_message("recovering abducible literals...");
    LiteralGeneratorT LGenerator(Loader);
    if (opts.impgen.input_type == gpid::AbducibleInputType::FILE) {
        LGenerator.load(opts.impgen.input_file);
    } else {
        LGenerator.generate(opts.impgen.input_generator);
    }

    l_message("create decomposition engine...");
    ImpgenAlgorithm<EngineT, LiteralGeneratorT>
        Generator(Loader, LGenerator, opts, opts.impgen);

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

template<class InterfaceT, class LiteralGeneratorT>
static inline void generate(OptionStorage& opts) {
    if (opts.naive) {
        generate_upae_x<NaiveAbducibleEngine<InterfaceT>, LiteralGeneratorT>(opts);
    } else {
        generate_upae_x<AdvancedAbducibleEngine<InterfaceT>, LiteralGeneratorT>(opts);
    }
}

#include "sai/impgen-executors.hpp"

static inline impgenExecutionStatus generate(OptionStorage& opts) {
    return wrap_generate(opts);
}

#endif
