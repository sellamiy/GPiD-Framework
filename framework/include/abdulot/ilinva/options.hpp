/**
 * \file abdulot/ilinva/options.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__ILINVA__OPTIONS_HPP
#define ABDULOT__ILINVA__OPTIONS_HPP

#include <string>
#include <limits>

namespace abdulot {
namespace ilinva {

    struct IlinvaOptions {

        std::string input_file;

        std::string output;

        uint32_t max_depth = std::numeric_limits<uint32_t>::max();

        std::string abd_override;

        bool disjunct = true;
        bool insurance_checks = true;

        bool shuffle_literals = false;

        uint32_t max_strengthening_size = std::numeric_limits<uint32_t>::max() - 1;

        uint64_t smt_time_limit = 0;
        double small_smt_time_limit = 0;

        std::map<std::string, std::string> handler_options;
    };

}
}

#endif
