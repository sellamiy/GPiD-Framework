#ifndef GPID_EXEC__UTILS__ILINVA_WRAPPERS_HPP
#define GPID_EXEC__UTILS__ILINVA_WRAPPERS_HPP

#include <abdulot/ilinva/engine-dual.hpp>
#include "ilinva-executors.hpp"

using namespace snlog;
using namespace abdulot::ilinva;

enum class ilinvaExecutionStatus { SUCCESS, FAILURE };

template<class CodeHandlerT, class InterfaceT>
static inline void generate(OptionStorage& opts) {
    generate_ilnt_x<DualInvariantEngine<CodeHandlerT, InterfaceT>>(opts);
}

#include "ilinva/executors.hpp"

static inline ilinvaExecutionStatus generate(OptionStorage& opts) {
    return wrap_generate(opts);
}

#endif
