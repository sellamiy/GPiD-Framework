#ifndef GPID_EXEC__UTILS__ILINVA_EXECUTORS_HPP
#define GPID_EXEC__UTILS__ILINVA_EXECUTORS_HPP

#include "ilinva-options.hpp"

using namespace snlog;
using namespace gpid;

template<class EngineT>
static inline void generate_ilnt_x(OptionStorage& opts) {
    // TODO: Handle Errors on subcalls
    l_message() << "init engine..." << l_end;
    IlinvaAlgorithm<EngineT>::printInfos();        

    l_message() << "create program engine..." << l_end;
    typename EngineT::CodeHandlerT ICH(opts.ilinva.input_file);

    l_message() << "create generation engine..." << l_end;
    IlinvaAlgorithm<EngineT> Generator(ICH, opts, opts.ilinva);

    l_message() << "generate loop invariants..." << l_end;
    opts.control.time.registerTime("generation");
    Generator.execute();
    opts.control.time.registerTime("generation-end");
}

#endif
