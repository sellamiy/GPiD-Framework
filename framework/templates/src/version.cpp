#define GPID_FRAMEWORK__REFERENCE__VERSION_CPP
#include <gpid/reference/version.hpp>

extern const std::string gpid::project_name
 = "GPiD Framework";
extern const std::string gpid::project_full_name
 = "Generic Abduction and Prime Implicate Generator Framework - GPiD";

extern const std::string gpid::project_version_major
 = "{{ data.version_major }}";
extern const std::string gpid::project_version_minor
 = "{{ data.version_minor }}";
extern const std::string gpid::project_version_patch
 = "{{ data.version_patch }}";

extern const std::string gpid::project_mode
 = "{{ data.mode }}";

extern const std::string gpid::project_version_devref
 = "{{ data.version_devref }}";
extern const std::string gpid::project_version_devloc
 = "{{ data.version_devloc }}";
extern const std::string gpid::project_version_state
 = "{{ data.version_state }}";

extern const std::string gpid::project_timestamp_configure
 = "{{ data.timestamp }}";
extern const std::string gpid::project_timestamp_build
 = __DATE__ "+" __TIME__;

extern const std::string gpid::version_message
 = "GPiD Framework Version "
   "{{ data.version_major }}.{{ data.version_minor }}.{{ data.version_patch }}-{{ data.mode }}\n"
   "Instrumentation {{ data.instrumentation }}\n"
   "Generic Abduction and Prime Implicate Generator Framework - GPiD\n"
   "Repository version status: "
   "{{ data.version_devref }}:{{ data.version_devloc }} - {{ data.version_state }}\n"
   "Configuration: {{ data.timestamp }}\n"
   "Build: " __DATE__ "+" __TIME__
    ;

