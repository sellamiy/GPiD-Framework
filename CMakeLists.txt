# = CMakeLists for Building the GPiD framework library and executable tools
# ==============================================================================
# Global project configuration
# ==============================================================================
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/include/")
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/modules/")
# ------------------------------------------------------------------------------
include(LoadVersionFile)
# ==============================================================================
cmake_minimum_required(VERSION 3.5 FATAL_ERROR)
project(abdulot-framework LANGUAGES CXX)
set    (EXTENDED_PROJECT_NAME "Abdulot Framework - Abduction Modulo Theories")
string (TIMESTAMP PROJECT_CFG_TIMESTAMP "%Y-%m-%d+%H:%M:%S")
configure_file("${CMAKE_SOURCE_DIR}/version.yml.in" "${CMAKE_BINARY_DIR}/version.yml")
load_version_file("${CMAKE_BINARY_DIR}/version.yml")
# ------------------------------------------------------------------------------
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib")
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
set(TESTS_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/test-bin")
# ------------------------------------------------------------------------------
message(STATUS "Libraries target directory: ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}")
message(STATUS "Executables target directory: ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")
message(STATUS "Tests target directory: ${TESTS_RUNTIME_OUTPUT_DIRECTORY}")
# ------------------------------------------------------------------------------
set(CMAKE_CXX_STANDARD 11)
if (WIN32)
else()
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")
  if (CMAKE_BUILD_TYPE STREQUAL "Debug")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-inline")
  endif()
endif()
# ------------------------------------------------------------------------------
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING
    "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
endif()
# ------------------------------------------------------------------------------
if (APPLE)
  include_directories(/usr/local/include)
  link_directories(/usr/local/lib)
endif()
# ------------------------------------------------------------------------------
set(LOCAL_LIB_HEADERS_DIR "${CMAKE_BINARY_DIR}/local/lib/include")
set(LOCAL_LIB_SOURCES_DIR "${CMAKE_BINARY_DIR}/local/lib/cxx")

set(LOCAL_SOLVER_INTERFACES_CONFIGS "${CMAKE_BINARY_DIR}/local/solver-interfaces/configs")
set(LOCAL_SOLVER_INTERFACES_INCLUDE "${CMAKE_BINARY_DIR}/local/solver-interfaces/include")
set(LOCAL_SOLVER_INTERFACES_SOURCES "${CMAKE_BINARY_DIR}/local/solver-interfaces/src")

set(LOCAL_IPH_CONFIGS "${CMAKE_BINARY_DIR}/local/iphandle/configs")
set(LOCAL_IPH_INCLUDE "${CMAKE_BINARY_DIR}/local/iphandle/include")
set(LOCAL_IPH_SOURCES "${CMAKE_BINARY_DIR}/local/iphandle/src")

set(LOCAL_MPCONTEXT_CONFIGS "${CMAKE_BINARY_DIR}/local/minpart-context/configs")
set(LOCAL_MPCONTEXT_INCLUDE "${CMAKE_BINARY_DIR}/local/minpart-context/include")
set(LOCAL_MPCONTEXT_SOURCES "${CMAKE_BINARY_DIR}/local/minpart-context/src")

set(LOCAL_FRAMEWORK_HEADERS_DIR "${CMAKE_BINARY_DIR}/local/framework/include")
set(LOCAL_FRAMEWORK_SOURCES_DIR "${CMAKE_BINARY_DIR}/local/framework/cxx")

set(LOCAL_EXEC_INCLUDE_DIR "${CMAKE_BINARY_DIR}/local/tools/include")
set(LOCAL_EXEC_SOURCES_DIR "${CMAKE_BINARY_DIR}/local/tools/src")

set(LOCAL_SAL_CMAKE_DIR "${CMAKE_BINARY_DIR}/local/sal/cmake")
# ==============================================================================
# Local project configuration
# ==============================================================================
include(FrameworkConfigurationOptions)
include(ExternalProject)
include(FrameworkCoverage)
include(FrameworkCosystems)
include(FrameworkDocumentation)
include(FrameworkExecWrapping)
# ------------------------------------------------------------------------------
if(NOT FRAMEWORK_WRAPPING_LANGUAGE)
  set(FRAMEWORK_WRAPPING_LANGUAGE "Python3" CACHE STRING
    "Choose the language of the framework global wrapper" FORCE)
endif()
set(FRAMEWORK_WRAPPING_EXECUTABLES CACHE INTERNAL "Wrapped executables")
function(register_executable name)
  add_executable(${name} ${ARGN})
  list(APPEND FRAMEWORK_WRAPPING_EXECUTABLES ${name})
  set(FRAMEWORK_WRAPPING_EXECUTABLES ${FRAMEWORK_WRAPPING_EXECUTABLES} CACHE INTERNAL "Wrapped executables")
endfunction()
# ==============================================================================
# Targets
# ==============================================================================
add_subdirectory(lib)

add_subdirectory(framework)

if(BUILD_GPID OR BUILD_ILINVA)
  add_subdirectory(solvers)
endif()

if(BUILD_ILINVA)
  add_subdirectory(iphandle)
endif()

if(BUILD_MINPART)
  add_subdirectory(mpcontext)
endif()

add_subdirectory(tools)

if(BUILD_TESTS)
  enable_testing()
  add_subdirectory(test)
endif()

if(BUILD_UTILITIES)
  add_subdirectory(utils)
endif()

if(BUILD_GLOBAL_WRAPPER)
  generate_wrapper(TARGET "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/abdulot-select"
    LANGUAGE ${FRAMEWORK_WRAPPING_LANGUAGE}
    EXECUTABLES ${FRAMEWORK_WRAPPING_EXECUTABLES})
endif()

add_custom_target(uninstall "${CMAKE_COMMAND}" -P "${CMAKE_SOURCE_DIR}/cmake/modules/Uninstall.cmake")
