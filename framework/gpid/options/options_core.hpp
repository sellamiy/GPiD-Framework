#ifndef GPID_OPTIONS_HPP
#define GPID_OPTIONS_HPP

#include <gpid/options/options_engine.hpp>

namespace gpid {

    struct CoreOptions {

        EngineOptions engine;

    };

    enum OptionStatus {
	OK
    };

    extern OptionStatus parseOptions(CoreOptions& opts, char** data);

};

#endif
