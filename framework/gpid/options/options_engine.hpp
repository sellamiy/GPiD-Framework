#ifndef GPID_DECOMP_ENGINE_OPTIONS_HPP
#define GPID_DECOMP_ENGINE_OPTIONS_HPP

namespace gpid {

    struct EngineOptions {

        bool print_implicates = true;
        bool store_implicates = false;

        bool use_models = true;

        bool allow_inconsistencies = false;

    };

};

#endif
