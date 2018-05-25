/**
 * \file gpid/options/options_abducibles.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__OPTIONS__ABDUCIBLES_HPP
#define GPID_FRAMEWORK__OPTIONS__ABDUCIBLES_HPP

#include <string>

namespace gpid {

    enum class AbdInputType { ABDIT_FILE, ABDIT_GENERATOR };
    inline const std::string to_string(const AbdInputType& it)
    { return it == AbdInputType::ABDIT_FILE ? "Abd?Type:file" : "Abd?Type:generator"; }

    /** \brief Options for the abducible hypotheses. \ingroup gpidcorelib */
    struct AbduciblesOptions {

        /** Method for recovering abducibles hypotheses */
        AbdInputType input_type = AbdInputType::ABDIT_GENERATOR;
        /** If input_type == FILE, filename to load hypotheses from */
        std::string input_file;
        /** If input_type == GENERATOR, id of an hypotheses generator */
        std::string input_generator = "<none>";

    };

};

#endif
