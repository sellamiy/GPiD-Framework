#ifndef GPID_FRAMEWORK__OPTIONS__ENGINE_HPP
#define GPID_FRAMEWORK__OPTIONS__ENGINE_HPP

#include <limits>

namespace gpid {

    struct EngineOptions {

        bool print_implicates = true;
        bool store_implicates = false;

        bool use_models = true;

        bool allow_inconsistencies = false;

        uint32_t max_level = std::numeric_limits<uint32_t>::max();

        uint64_t time_limit = 0;

    };

};

#endif
