##########
# Alt-Ergo SMT Solver Executable Finder
##########
find_program(
  AltErgo_EXECUTABLE
  NAMES alt-ergo
  DOC "Alt-Ergo SMT Solver"
)
mark_as_advanced(AltErgo_EXECUTABLE)

# Version
if (AltErgo_EXECUTABLE)
  execute_process (COMMAND ${AltErgo_EXECUTABLE} -version
    OUTPUT_VARIABLE AltErgo_VERSION_STRING
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE)
endif()
mark_as_advanced(AltErgo_VERSION_STRING)

# Config
find_package_handle_standard_args(
  AltErgo
  REQUIRED_VARS AltErgo_EXECUTABLE
  VERSION_VAR AltErgo_VERSION_STRING
)
