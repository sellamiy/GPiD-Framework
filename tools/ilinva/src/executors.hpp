#ifndef GPID_EXEC__UTILS__ILINVA_EXECUTORS_HPP
#define GPID_EXEC__UTILS__ILINVA_EXECUTORS_HPP

#include <abdulot/ilinva/algorithm-ilinva.hpp>
#include "options.hpp"

using namespace snlog;
using namespace abdulot::ilinva;

static inline bool is_str_true(const std::string& s) {
    return s == "true" || s == "TRUE" || s == "True";
}

static inline bool is_str_false(const std::string& s) {
    return s == "false" || s == "FALSE" || s == "False";
}

template<class EngineT>
static inline void generate_ilnt_x(OptionStorage& opts) {
    // TODO: Handle Errors on subcalls
    l_message() << "init engine..." << l_end;
    IlinvaAlgorithm<EngineT>::printInfos();        

    l_message() << "create program engine..." << l_end;
    typename EngineT::ProblemHandlerT IPH
        (opts.ilinva.input_file, opts.ilinva.abd_override.length() > 0, opts.ilinva.shuffle_literals);
    for (const std::pair<std::string, std::string>& hopt : opts.ilinva.handler_options) {
        if (is_str_true(hopt.second))
            IPH.setOption(hopt.first, true);
        else if (is_str_false(hopt.second))
            IPH.setOption(hopt.first, false);
        else
            IPH.setOption(hopt.first, hopt.second);
    }

    l_message() << "create generation engine..." << l_end;
    IlinvaAlgorithm<EngineT> Generator(IPH, opts, opts.ilinva);

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
