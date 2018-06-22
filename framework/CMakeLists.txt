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

load_version_file("${CMAKE_BINARY_DIR}/version.yml")
register_version_generator("${CMAKE_BINARY_DIR}/version.yml" "${LOCAL_FRAMEWORK_SOURCES_DIR}/version.cpp")
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

target_link_libraries(gpid-core-static starray-static lcdot-static snlog)
target_link_libraries(gpid-core-shared starray-shared lcdot-shared snlog)

if(GPID_INSTRUMENTATION)
  target_link_libraries(gpid-core-static pctrace-static)
  target_link_libraries(gpid-core-shared pctrace-shared)
endif()
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
