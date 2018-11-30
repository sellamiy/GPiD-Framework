# ==============================================================================
# GPiD Framework library target configuration
# ==============================================================================
project(libgpid LANGUAGES CXX)
include(LoadVersionFile)
# ==============================================================================
# Files configuration
# ==============================================================================
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/core/config.hpp.in
  ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/core/config.hpp)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/gpid.hpp.in
  ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/gpid.hpp)

register_version_generator(version-sources "${CMAKE_BINARY_DIR}/version.yml"
  "${LOCAL_FRAMEWORK_SOURCES_DIR}/version.cpp")
# ==============================================================================
# Locating and selecting library sources
# ==============================================================================
file(GLOB SRC_GPID_CORE
  "${LOCAL_FRAMEWORK_SOURCES_DIR}/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/*/*.cpp"
  )
list(APPEND SRC_GPID_CORE "${LOCAL_FRAMEWORK_SOURCES_DIR}/version.cpp")
list(FILTER SRC_GPID_CORE EXCLUDE REGEX
  "${CMAKE_CURRENT_SOURCE_DIR}/src/instrument/[a-z]+\.cpp")

file(GLOB SRC_GPID_INSTRUMENT
  "${CMAKE_CURRENT_SOURCE_DIR}/src/instrument/*.cpp")
# ==============================================================================
# Library target definition
# ==============================================================================
if(GPID_INSTRUMENTATION)
  add_library(gpid-core-static STATIC ${SRC_GPID_CORE} ${SRC_GPID_INSTRUMENT})
  add_library(gpid-core-shared SHARED ${SRC_GPID_CORE} ${SRC_GPID_INSTRUMENT})
else()
  add_library(gpid-core-static STATIC ${SRC_GPID_CORE})
  add_library(gpid-core-shared SHARED ${SRC_GPID_CORE})
endif()

add_dependencies(gpid-core-static version-sources)
add_dependencies(gpid-core-static version-sources)

target_include_directories(gpid-core-static
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_FRAMEWORK_HEADERS_DIR}"
  PRIVATE "${LOCAL_FRAMEWORK_SOURCES_DIR}")
target_include_directories(gpid-core-shared
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_FRAMEWORK_HEADERS_DIR}"
  PRIVATE "${LOCAL_FRAMEWORK_SOURCES_DIR}")

set_target_properties(gpid-core-static PROPERTIES
  OUTPUT_NAME gpid-core
  VERSION ${VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(gpid-core-shared PROPERTIES
  OUTPUT_NAME gpid-core
  VERSION ${VERSION}
  CLEAN_DIRECT_OUTPUT 1)

target_link_libraries(gpid-core-static
  stdutils-static starray-static lcdot-static smtlib2tools-static snlog)
target_link_libraries(gpid-core-shared
  stdutils-shared starray-shared lcdot-shared smtlib2tools-shared snlog)
# ==============================================================================
# Install framework
# ==============================================================================
install(TARGETS gpid-core-static gpid-core-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/gpid
  DESTINATION include FILES_MATCHING PATTERN "*.hpp")
install(FILES ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/core/config.hpp
  DESTINATION include/gpid/core)
install(FILES ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/gpid.hpp
  DESTINATION include/gpid)
# ==============================================================================
