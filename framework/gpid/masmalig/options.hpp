/**
 * \file gpid/masmalig/options.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__MASMALIG__OPTIONS_HPP
#define GPID_FRAMEWORK__MASMALIG__OPTIONS_HPP

#include <string>
#include <vector>
#include <limits>

namespace gpid {

    /** Options for the smart literal generator algorithm. */
    struct MasmaligOptions {

        /* List of smtlibv2 source files to load */
        std::vector<std::string> source_files;
        /* List of mlb script files to load */
        std::vector<std::string> script_files;
        /* List of mlw whyml files to load */
        std::vector<std::string> whyml_files;

        /* List of production rules for generation */
        std::vector<std::string> targets;

    };

}

#endif
