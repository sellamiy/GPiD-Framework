#ifndef GPID_OPTIONS_HPP
#define GPID_OPTIONS_HPP

#include <gpid/options/options_engine.hpp>

namespace gpid {

    struct CoreOptions {

	std::string input;

        EngineOptions engine;

    };

    enum OptionStatus {
	OK, ENDED, FAILURE
    };

    extern OptionStatus parseOptions(CoreOptions& opts, int argc, char** argv);

};

#endif
