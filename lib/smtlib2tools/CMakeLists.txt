# ==============================================================================
# Smtlib2 C++ tools library - local library target
# ==============================================================================
project(libsmtlib2tools LANGUAGES CXX)
set(LIBSMTLIB2_CPP_VERSION "0.4.0")
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/smtlib2tools/smtlib2tools.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/smtlib2tools/smtlib2tools.hpp)

file(GLOB LIBSMTLIB2_CPP_HEADERS "smtlib2tools/*.hpp")
file(GLOB LIBSMTLIB2_CPP_SOURCES "src/*.cpp")
# ------------------------------------------------------------------------------
add_library(smtlib2tools-static STATIC ${LIBSMTLIB2_CPP_SOURCES})
add_library(smtlib2tools-shared SHARED ${LIBSMTLIB2_CPP_SOURCES})
target_link_libraries(smtlib2tools-static snlog lisptp-static stdutils-static)
target_link_libraries(smtlib2tools-shared snlog lisptp-shared stdutils-shared)
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
# ------------------------------------------------------------------------------
register_executable(smtlib2-tools "bin/smtlib2-tools.cpp")
target_link_libraries(smtlib2-tools smtlib2tools-static cxxopts)
# ------------------------------------------------------------------------------
install(TARGETS smtlib2tools-static smtlib2tools-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBSMTLIB2_CPP_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/smtlib2tools/smtlib2tools.hpp
  DESTINATION include/smtlib2tools)
install(TARGETS smtlib2-tools RUNTIME DESTINATION bin)
