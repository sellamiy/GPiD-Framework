#ifndef GPID_FRAMEWORK__VERSION_HPP
#define GPID_FRAMEWORK__VERSION_HPP

#include <string>

namespace gpid {

    extern const std::string project_name;
    extern const std::string project_full_name;

    extern const std::string project_version;
    extern const std::string project_version_refspec;
    extern const std::string project_version_commit;
    extern const std::string project_version_state;

    extern const std::string project_mode;

    extern const std::string project_timestamp_configure;
    extern const std::string project_timestamp_build;

    extern const std::string list_configured_generators();

    extern const std::string generate_version_message();

};

#endif
