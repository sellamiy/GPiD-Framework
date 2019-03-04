# *********************************
# Why3 Platform Executable Finder
# *********************************
find_program(
  WHY3_EXECUTABLE
  NAMES why3
  DOC "Why3 Platform"
)

mark_as_advanced(WHY3_EXECUTABLE)

# Version
if (WHY3_EXECUTABLE)
  execute_process (COMMAND ${WHY3_EXECUTABLE} --version
    OUTPUT_VARIABLE WHY3_VERSION_STRING
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE)
  string(REPLACE "Why3 platform, version " "" WHY3_VERSION "${WHY3_VERSION_STRING}")
endif()
mark_as_advanced(WHY3_VERSION)

# Config
find_package_handle_standard_args(
  Why3
  REQUIRED_VARS WHY3_EXECUTABLE
  VERSION_VAR WHY3_VERSION
)
