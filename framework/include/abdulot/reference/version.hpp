/**
 * \file abdulot/reference/version.hpp
 * \brief Abdulot Framework Version Header.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__REFERENCE__VERSION_HPP
#define ABDULOT__REFERENCE__VERSION_HPP

#include <string>

namespace abdulot {

    /** Name of the framework */
    extern const std::string project_name;
    /** Detailed name of the framework */
    extern const std::string project_full_name;

    /** Version of the framework */
    extern const std::string project_version;
    /** Major version of the framework */
    extern const std::string project_version_major;
    /** Minor version of the framework */
    extern const std::string project_version_minor;
    /** Patch version of the framework */
    extern const std::string project_version_patch;

    /** Compilation mode of the framework */
    extern const std::string project_mode;

    /** Development reference of the framework */
    extern const std::string project_version_devref;
    /** Development location of the framework */
    extern const std::string project_version_devloc;
    /** Development repository state of the framework */
    extern const std::string project_version_state;

    /** Project last configuration timestamp */
    extern const std::string project_timestamp_configure;
    /** Project compilation timestamp */
    extern const std::string project_timestamp_build;

    /** Complete version message of the framework */
    extern const std::string version_message;

};

#endif
