#ifndef GPID_OPTIONS_HPP
#define GPID_OPTIONS_HPP

#include <gpid/config.hpp>
#include <gpid/options/options_engine.hpp>
#include <gpid/options/options_abducibles.hpp>

namespace gpid {

    struct CoreOptions {

        AbduciblesOptions abducibles;
        EngineOptions engine;

    };

};

#endif
