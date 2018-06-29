/**
 * \file gpid/impgen/options.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__IMPGEN__OPTIONS_HPP
#define GPID_FRAMEWORK__IMPGEN__OPTIONS_HPP

#include <string>
#include <limits>

namespace gpid {

    enum class AbducibleInputType { FILE, GENERATOR };
    inline const std::string to_string(const AbducibleInputType& it)
    { return it == AbducibleInputType::FILE ? "Abd?Type:file" : "Abd?Type:generator"; }

    /** \brief Options for the implicate generator algorithm. \ingroup gpidcorelib */
    struct ImpgenOptions {

        /** Print implicates on terminal when generated */
        bool print_implicates = false;
        /** Store generated implicates and skipp storage-subsumed hypotheses */
        bool store_implicates = true;
        /** Print stored implicates after computation */
        bool print_storage = false;
        /** Export stored implicates as graph after computation */
        bool export_storage = false;
        /** Location to export storage to */
        std::string export_storage_location;

        /** Use models returned by solvers to filter hypotheses */
        bool use_models = true;

        /** Do not skip inconsistent hypotheses sets */
        bool allow_inconsistencies = false;

        /** Skip literals detected as consequences of previous assignments */
        bool detect_consequences = false;

        /** Maximal number of abducible hypotheses in an implicate */
        uint32_t max_level = std::numeric_limits<uint32_t>::max();

        /** Maximal number of implicates to generate */
        uint64_t implicate_limit = std::numeric_limits<uint64_t>::max();

        /** Method for recovering abducibles hypotheses */
        AbducibleInputType input_type = AbducibleInputType::GENERATOR;
        /** If input_type == FILE, filename to load hypotheses from */
        std::string input_file;
        /** If input_type == GENERATOR, id of an hypotheses generator */
        std::string input_generator = "<none>";

    };

}

#endif
