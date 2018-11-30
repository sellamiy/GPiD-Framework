# ==============================================================================
# Smtlib2 C++ tools library - local library target
# ==============================================================================
project(libsmtlib2tools LANGUAGES CXX)
set(LIBSMTLIB2_CPP_VERSION "0.2.1")
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/smtlib2tools/smtlib2tools.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/smtlib2tools/smtlib2tools.hpp)

file(GLOB LIBSMTLIB2_CPP_HEADERS "smtlib2tools/*.hpp")
file(GLOB LIBSMTLIB2_CPP_SOURCES "src/*.cpp")
# ------------------------------------------------------------------------------
add_library(smtlib2tools-static STATIC ${LIBSMTLIB2_CPP_SOURCES})
add_library(smtlib2tools-shared SHARED ${LIBSMTLIB2_CPP_SOURCES})
target_link_libraries(smtlib2tools-static snlog whymlp-static ugly)
target_link_libraries(smtlib2tools-shared snlog whymlp-shared ugly)
target_include_directories(smtlib2tools-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
target_include_directories(smtlib2tools-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
set_target_properties(smtlib2tools-static PROPERTIES
  OUTPUT_NAME smtlib2tools
  VERSION ${LIBSMTLIB2_CPP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(smtlib2tools-shared PROPERTIES
  OUTPUT_NAME smtlib2tools
  VERSION ${LIBSMTLIB2_CPP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS smtlib2tools-static smtlib2tools-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBSMTLIB2_CPP_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/smtlib2tools/smtlib2tools.hpp
  DESTINATION include/smtlib2tools)
