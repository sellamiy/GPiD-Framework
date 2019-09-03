##########
# VeriT SMT Solver Executable Finder
##########
find_program(
  VERIT_EXECUTABLE
  NAMES veriT
  DOC "veriT SMT Solver"
)
mark_as_advanced(VERIT_EXECUTABLE)

# Version
if (VERIT_EXECUTABLE)
  execute_process (COMMAND ${VERIT_EXECUTABLE} --version
    OUTPUT_VARIABLE VERIT_VERSION_STRING
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE)
  string(REPLACE "This is veriT, version " "" VERIT_VERSION "${VERIT_VERSION_STRING}")
endif()
mark_as_advanced(VERIT_VERSION)

# Config
find_package_handle_standard_args(
  VeriT
  REQUIRED_VARS VERIT_EXECUTABLE
  VERSION_VAR VERIT_VERSION
)
