# - Try to find CVC4
# CVC4_FOUND - system has CVC4 lib
# CVC4_INCLUDE_DIR - CVC4 include directory
# CVC4_LIBRARIES - Libraries needed to use CVC4

find_path(CVC4_INCLUDE_DIR NAMES "cvc4/cvc4.h")
find_library(CVC4_LIBRARIES NAMES cvc4 libcvc4)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CVC4 DEFAULT_MSG CVC4_INCLUDE_DIR CVC4_LIBRARIES)

mark_as_advanced(CVC4_INCLUDE_DIR CVC4_LIBRARIES)
