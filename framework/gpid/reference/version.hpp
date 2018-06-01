/**
 * \file gpid/reference/version.hpp
 * \brief GPiD-Framework Version Header.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__REFERENCE__VERSION_HPP
#define GPID_FRAMEWORK__REFERENCE__VERSION_HPP

#include <string>

namespace gpid {

    extern const std::string project_name;
    extern const std::string project_full_name;

    extern const std::string project_version_major;
    extern const std::string project_version_minor;
    extern const std::string project_version_patch;

    extern const std::string project_mode;

    extern const std::string project_version_devref;
    extern const std::string project_version_devloc;
    extern const std::string project_version_state;

    extern const std::string project_timestamp_configure;
    extern const std::string project_timestamp_build;

    extern const std::string version_message;

};

#endif
