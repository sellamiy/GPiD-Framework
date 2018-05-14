/**
 * \file gpid/options/options_engine.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__OPTIONS__ENGINE_HPP
#define GPID_FRAMEWORK__OPTIONS__ENGINE_HPP

#include <limits>

namespace gpid {

    /** \brief Options structure for the implicate generator. \ingroup gpidcorelib */
    struct EngineOptions {

        /** Print implicates on terminal when generated */
        bool print_implicates = false;
        /** Store generated implicates and skipp storage-subsumed hypotheses */
        bool store_implicates = false;
        /** Print stored implicates after computation */
        bool print_storage = false;
        /** Export stored implicates as graph after computation */
        bool export_storage = false;

        /** Use models returned by solvers to filter hypotheses */
        bool use_models = true;

        /** Do not skip inconsistent hypotheses sets */
        bool allow_inconsistencies = false;

        /** Skip literals detected as consequences of previous assignments */
        bool detect_consequences = true;

        /** Maximal number of abducible hypotheses in an implicate */
        uint32_t max_level = std::numeric_limits<uint32_t>::max();

        /** Timeout */
        uint64_t time_limit = 0;

        /** Maximal number of implicates to generate */
        uint64_t implicate_limit = std::numeric_limits<uint64_t>::max();

    };

};

#endif
