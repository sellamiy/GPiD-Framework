#ifndef GPID_EXEC__UTILS__IMPGEN_WRAPPERS_HPP
#define GPID_EXEC__UTILS__IMPGEN_WRAPPERS_HPP

#include "impgen-executors.hpp"
#include "guniti-executors.hpp"

using namespace snlog;
using namespace gpid;

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

#include "sai/impgen-executors.hpp"

static inline impgenExecutionStatus generate(OptionStorage& opts) {
    return wrap_generate(opts);
}

#endif
