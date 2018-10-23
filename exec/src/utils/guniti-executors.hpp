#ifndef GPID_EXEC__UTILS__GUNITI_EXECUTORS_HPP
#define GPID_EXEC__UTILS__GUNITI_EXECUTORS_HPP

#include "guniti-options.hpp"

using namespace snlog;
using namespace gpid;

enum class gunitiExecutionStatus { SUCCESS, FAILURE };

template<typename InterfaceT, typename LiteralGeneratorT>
static inline void generate_upae_x(OptionStorage& opts) {
    using GunitImplicateHandler = BasicImplicateHandler<GunitiEngine<InterfaceT>>;
    // TODO: Handle Errors on subcalls
    l_message() << "init engine..." << l_end;
    GunitiAlgorithm<InterfaceT, LiteralGeneratorT, GunitImplicateHandler>::printInfos();

    l_message() << "load problem..." << l_end;
    typename GunitiAlgorithm<InterfaceT, LiteralGeneratorT, GunitImplicateHandler>
        ::ProblemLoaderT Loader;
    Loader.load(opts.input, opts.input_lang);

    l_message() << "recovering abducible literals..." << l_end;
    LiteralGeneratorT LGenerator(Loader);
    if (opts.guniti.input_type == gpid::AbducibleInputType::FILE) {
        LGenerator.load(opts.guniti.input_file);
    } else {
        LGenerator.generate(opts.guniti.input_generator);
    }

    l_message() << "create decomposition engine..." << l_end;
    GunitImplicateHandler
        ihandler(opts.guniti.print_implicates, opts.guniti.store_implicates);
    GunitiAlgorithm<InterfaceT, LiteralGeneratorT, GunitImplicateHandler>
        Generator(Loader, LGenerator, ihandler, opts, opts.guniti);

    l_message() << "generate implicates..." << l_end;
    opts.control.time.registerTime("generation");
    Generator.execute();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of implicates generated",
                                    Generator.getGeneratedImplicatesCount());
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Nodes skipped", "");
    for (std::pair<std::string, GPiDAlgorithm::counter_t> p : Generator.getSkippedCounts()) {
        opts.control.stats.addStatistic(p.first, p.second, 4);
    }
}

template<class InterfaceT, class LiteralGeneratorT>
static inline void generate(OptionStorage& opts) {
    generate_upae_x<InterfaceT, LiteralGeneratorT>(opts);
}

#include "sai/guniti-executors.hpp"

static inline gunitiExecutionStatus generate(OptionStorage& opts) {
    return wrap_generate(opts);
}

#endif
