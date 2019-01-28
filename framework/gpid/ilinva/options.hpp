/**
 * \file gpid/ilinva/options.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__ILINVA__OPTIONS_HPP
#define GPID_FRAMEWORK__ILINVA__OPTIONS_HPP

#include <string>
#include <limits>

namespace gpid {

    struct IlinvaOptions {

        std::string input_file;

        std::string output;

        uint32_t max_depth = std::numeric_limits<uint32_t>::max();

        std::string abd_override;

        bool disjunct = true;

        uint32_t max_strengthening_size = std::numeric_limits<uint32_t>::max() - 1;

        uint64_t smt_time_limit = 0;

    };

}

#endif
