# ==============================================================================
# Abdulot Framework library target configuration
# ==============================================================================
project(libabdulot LANGUAGES CXX)
include(LoadVersionFile)
# ==============================================================================
# Files configuration
# ==============================================================================
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/include/abdulot/core/config.hpp.in
  ${LOCAL_FRAMEWORK_HEADERS_DIR}/abdulot/core/config.hpp)

register_version_generator(version-sources "${CMAKE_BINARY_DIR}/version.yml"
  "${LOCAL_FRAMEWORK_SOURCES_DIR}/version.cpp")
# ==============================================================================
# Locating and selecting library sources
# ==============================================================================
file(GLOB SRC_ABDULOT_CORE
  "${LOCAL_FRAMEWORK_SOURCES_DIR}/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/core/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/gpid/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/ilinva/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/saihelpers/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/utils/*.cpp"
  )
list(APPEND SRC_ABDULOT_CORE "${LOCAL_FRAMEWORK_SOURCES_DIR}/version.cpp")

file(GLOB SRC_ABDULOT_INSTRUMENT
  "${CMAKE_CURRENT_SOURCE_DIR}/src/instrument/*.cpp")
# ==============================================================================
# Library target definition
# ==============================================================================
if(INSTRUMENTATION)
  add_library(abdulot-static STATIC ${SRC_ABDULOT_CORE} ${SRC_ABDULOT_INSTRUMENT})
  add_library(abdulot-shared SHARED ${SRC_ABDULOT_CORE} ${SRC_ABDULOT_INSTRUMENT})
else()
  add_library(abdulot-static STATIC ${SRC_ABDULOT_CORE})
  add_library(abdulot-shared SHARED ${SRC_ABDULOT_CORE})
endif()

add_dependencies(abdulot-static version-sources)
add_dependencies(abdulot-static version-sources)

target_include_directories(abdulot-static
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${LOCAL_FRAMEWORK_HEADERS_DIR}"
  PRIVATE "${LOCAL_FRAMEWORK_SOURCES_DIR}")
target_include_directories(abdulot-shared
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${LOCAL_FRAMEWORK_HEADERS_DIR}"
  PRIVATE "${LOCAL_FRAMEWORK_SOURCES_DIR}")

set_target_properties(abdulot-static PROPERTIES
  OUTPUT_NAME abdulot
  VERSION ${VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(abdulot-shared PROPERTIES
  OUTPUT_NAME abdulot
  VERSION ${VERSION}
  CLEAN_DIRECT_OUTPUT 1)

target_link_libraries(abdulot-static
  stdutils-static starray-static lcdot-static smtlib2tools-static snlog)
target_link_libraries(abdulot-shared
  stdutils-shared starray-shared lcdot-shared smtlib2tools-shared snlog)
# ==============================================================================
# Install framework
# ==============================================================================
install(TARGETS abdulot-static abdulot-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/include/abdulot
  DESTINATION include FILES_MATCHING PATTERN "*.hpp")
install(FILES ${LOCAL_FRAMEWORK_HEADERS_DIR}/abdulot/core/config.hpp
  DESTINATION include/abdulot/core)
# ==============================================================================
