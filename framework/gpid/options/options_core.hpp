#ifndef GPID_FRAMEWORK__OPTIONS__CORE_HPP
#define GPID_FRAMEWORK__OPTIONS__CORE_HPP

#include <gpid/config.hpp>
#include <gpid/options/options_engine.hpp>
#include <gpid/options/options_abducibles.hpp>

#include <gpid/options/options_instrument.hpp>

namespace gpid {

    struct CoreOptions {

        AbduciblesOptions abducibles;
        EngineOptions engine;

        instrument::InstrumentOptions instrument;

    };

};

#endif
