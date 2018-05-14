# ==============================================================================
# GPiD Framework library target configuration
# ==============================================================================
project(libgpid LANGUAGES CXX)
# ==============================================================================
# Files configuration
# ==============================================================================
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/config.hpp.in
  ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/config.hpp)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/gpid.hpp.in
  ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/gpid.hpp)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/errors.hpp.in
  ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/errors.hpp)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/src/config/version.cpp.in
  ${LOCAL_FRAMEWORK_SOURCES_DIR}/config/version.cpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/version.hpp
  ${LOCAL_FRAMEWORK_HEADERS_DIR}/gpid/version.hpp COPYONLY)

# ==============================================================================
# Locating and selecting library sources
# ==============================================================================
file(GLOB SRC_GPID_CORE
  "${LOCAL_FRAMEWORK_SOURCES_DIR}/config/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/util/*.cpp"
)

if(GPID_INSTRUMENTATION)
  file(GLOB SRC_GPID_INSTRUMENT
    "${CMAKE_CURRENT_SOURCE_DIR}/src/instrument/*.cpp"
    "${FRAMEWORK_CONF_SOURCE_DIR}/instrument/*.cpp"
  )
endif()
# ==============================================================================
# Library target definition
# ==============================================================================
add_library(gpid-core-static STATIC ${SRC_GPID_CORE} ${SRC_GPID_INSTRUMENT})
add_library(gpid-core-shared SHARED ${SRC_GPID_CORE} ${SRC_GPID_INSTRUMENT})
target_include_directories(gpid-core-static
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_FRAMEWORK_HEADERS_DIR}"
  PRIVATE "${LOCAL_FRAMEWORK_SOURCES_DIR}")
target_include_directories(gpid-core-shared
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_FRAMEWORK_HEADERS_DIR}"
  PRIVATE "${LOCAL_FRAMEWORK_SOURCES_DIR}")
set_target_properties(gpid-core-static PROPERTIES OUTPUT_NAME gpid-core CLEAN_DIRECT_OUTPUT 1)
set_target_properties(gpid-core-shared PROPERTIES
  OUTPUT_NAME gpid-core
  VERSION ${VERSION}
  CLEAN_DIRECT_OUTPUT 1)
target_link_libraries(gpid-core-static starray-static dot-static snlog)
target_link_libraries(gpid-core-shared starray-shared dot-shared snlog)

if(GPID_INSTRUMENTATION)
  target_link_libraries(gpid-core-static pctrace-static)
  target_link_libraries(gpid-core-shared pctrace-shared)
endif()
