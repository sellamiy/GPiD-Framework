# ==============================================================================
# Standard C++ Utils Library - local library target
# ==============================================================================
project(libstdutils LANGUAGES CXX)
set(LIBSTDUTILS_VERSION "0.3.3")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/stdutils/stdutils.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/stdutils/stdutils.hpp)

file(GLOB LIBSTDUTILS_HEADERS "stdutils/*.hpp")
file(GLOB LIBSTDUTILS_SOURCES "src/*.cpp")

add_library(stdutils-static STATIC ${LIBSTDUTILS_SOURCES})
add_library(stdutils-shared SHARED ${LIBSTDUTILS_SOURCES})
target_include_directories(stdutils-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(stdutils-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(stdutils-static PROPERTIES
  OUTPUT_NAME stdutils
  VERSION ${LIBSTDUTILS_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(stdutils-shared PROPERTIES
  OUTPUT_NAME stdutils
  VERSION ${LIBSTDUTILS_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS stdutils-static stdutils-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBSTDUTILS_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/stdutils/stdutils.hpp
  DESTINATION include/stdutils)
