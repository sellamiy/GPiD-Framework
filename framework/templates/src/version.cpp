#define ABDULOT__REFERENCE__VERSION_CPP
#include <abdulot/reference/version.hpp>

extern const std::string abdulot::project_name
 = "Abdulot Framework";
extern const std::string abdulot::project_full_name
 = "Abduction Modulo Theories Abdulot Framework";

extern const std::string abdulot::project_version
 = "{{ data.version_major }}.{{ data.version_minor }}.{{ data.version_patch }}";
extern const std::string abdulot::project_version_major
 = "{{ data.version_major }}";
extern const std::string abdulot::project_version_minor
 = "{{ data.version_minor }}";
extern const std::string abdulot::project_version_patch
 = "{{ data.version_patch }}";

extern const std::string abdulot::project_mode
 = "{{ data.mode }}";

extern const std::string abdulot::project_version_devref
 = "{{ data.version_devref }}";
extern const std::string abdulot::project_version_devloc
 = "{{ data.version_devloc }}";
extern const std::string abdulot::project_version_state
 = "{{ data.version_state }}";

extern const std::string abdulot::project_timestamp_configure
 = "{{ data.timestamp }}";
extern const std::string abdulot::project_timestamp_build
 = __DATE__ "+" __TIME__;

extern const std::string abdulot::version_message
 = "Abdulot Framework Version "
   "{{ data.version_major }}.{{ data.version_minor }}.{{ data.version_patch }}-{{ data.mode }}\n"
   "Instrumentation {{ data.instrumentation }}\n"
   "Abduction Modulo Theories Abdulot Framework\n"
   "Repository version status: "
   "{{ data.version_devref }}:{{ data.version_devloc }} - {{ data.version_state }}\n"
   "Configuration: {{ data.timestamp }}\n"
   "Build: " __DATE__ "+" __TIME__
    ;

