#ifndef GPID_EXEC__UTILS__ILINVA_EXECUTORS_HPP
#define GPID_EXEC__UTILS__ILINVA_EXECUTORS_HPP

#include <abdulot/ilinva/algorithm-ilinva.hpp>
#include "options.hpp"

using namespace snlog;
using namespace abdulot::ilinva;

template<class EngineT>
static inline void generate_ilnt_x(OptionStorage& opts) {
    // TODO: Handle Errors on subcalls
    l_message() << "init engine..." << l_end;
    IlinvaAlgorithm<EngineT>::printInfos();        

    l_message() << "create program engine..." << l_end;
    typename EngineT::CodeHandlerT ICH(opts.ilinva.input_file, opts.ilinva.abd_override.length() > 0);

    l_message() << "create generation engine..." << l_end;
    IlinvaAlgorithm<EngineT> Generator(ICH, opts, opts.ilinva);

    l_message() << "generate loop invariants..." << l_end;
    opts.control.time.registerTime("generation");
    Generator.execute();
    opts.control.time.registerTime("generation-end");

    opts.control.stats.addStatisticGroup();
    opts.control.stats.addStatistic("Engine counters", "");
    for (auto stat : Generator.getEngineCounters()) {
        opts.control.stats.addStatistic(stat.first, stat.second, 4);
    }
}

#endif
