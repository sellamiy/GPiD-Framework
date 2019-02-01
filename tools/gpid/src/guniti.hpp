#ifndef GPID_EXEC__UTILS__GUNITI_EXECUTORS_HPP
#define GPID_EXEC__UTILS__GUNITI_EXECUTORS_HPP

#include <abdulot/gpid/algorithm-guniti.hpp>
#include "options.hpp"

using namespace snlog;
using namespace abdulot::gpid;

enum class gunitiExecutionStatus { SUCCESS, FAILURE };

template<typename InterfaceT, typename LiteralGeneratorT>
static inline void generate_upai_x(OptionStorage& opts) {
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
    if (opts.impgen.input_type == AbducibleInputType::FILE) {
        LGenerator.load(opts.impgen.input_file);
    } else {
        LGenerator.generate(opts.impgen.input_generator);
    }

    l_message() << "create decomposition engine..." << l_end;
    GunitImplicateHandler
        ihandler(opts.impgen.print_implicates, opts.impgen.store_implicates);
    GunitiAlgorithm<InterfaceT, LiteralGeneratorT, GunitImplicateHandler>
        Generator(Loader, LGenerator, ihandler, opts, opts.impgen);

    l_message() << "generate implicates..." << l_end;
    opts.control.time.registerTime("generation");
    Generator.execute();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Number of implicates generated",
                                    Generator.getGeneratedImplicatesCount());
    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Nodes skipped", "");
    for (std::pair<std::string, abdulot::Algorithm::counter_t> p : Generator.getSkippedCounts()) {
        opts.control.stats.addStatistic(p.first, p.second, 4);
    }
}

#endif
