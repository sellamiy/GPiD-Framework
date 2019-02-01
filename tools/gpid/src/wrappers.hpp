#ifndef GPID_EXEC__UTILS__IMPGEN_WRAPPERS_HPP
#define GPID_EXEC__UTILS__IMPGEN_WRAPPERS_HPP

#include <abdulot/gpid/engine-naive.hpp>
#include <abdulot/gpid/engine-advanced.hpp>
#include "executors.hpp"
#include "guniti.hpp"

using namespace snlog;
using namespace abdulot::gpid;

enum class impgenExecutionStatus { SUCCESS, FAILURE };

template<class InterfaceT, class LiteralGeneratorT>
static inline void generate(OptionStorage& opts) {
    if (opts.guniti_delegation && opts.impgen.max_level <= 2) {
        l_notif() << "Using GunitI delegation for small implicates generation" << l_end;
        generate_upai_x<InterfaceT, LiteralGeneratorT>(opts);
    } else if (opts.naive) {
        generate_upae_x<NaiveAbducibleEngine<InterfaceT>, LiteralGeneratorT>(opts);
    } else {
        generate_upae_x<AdvancedAbducibleEngine<InterfaceT>, LiteralGeneratorT>(opts);
    }
}

#include "gpid/generators.hpp"

static inline impgenExecutionStatus generate(OptionStorage& opts) {
    return wrap_generate(opts);
}

#endif
