# = CMakeLists for Building the GPiD framework library and executable tools
# ==============================================================================
# Global project configuration
# ==============================================================================
cmake_minimum_required(VERSION 3.5 FATAL_ERROR)
project(gpid-framework LANGUAGES CXX)
set    (EXTENDED_PROJECT_NAME "GPiD Framework - Prime Implicates by Decomposition")
string (TIMESTAMP PROJECT_CFG_TIMESTAMP "%Y-%m-%d+%H:%M:%S")

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/include/")
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/modules/")

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib")
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/lib")
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin")
set(TESTS_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/test-bin")

message(STATUS "Libraries target directory: ${CMAKE_LIBRARY_OUTPUT_DIRECTORY}")
message(STATUS "Executables target directory: ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}")
message(STATUS "Tests target directory: ${TESTS_RUNTIME_OUTPUT_DIRECTORY}")

set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")
if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-inline")
endif()

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING
    "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
endif()

set(LOCAL_LIBRARIES_DIRECTORY "${CMAKE_BINARY_DIR}/local/lib/include")
set(FRAMEWORK_CHEADERS_DIRECTORY "${CMAKE_BINARY_DIR}/local/framework/include")
set(FRAMEWORK_CSOURCES_DIRECTORY "${CMAKE_BINARY_DIR}/local/framework/cxx")

include(GetGitRevisionDescription)
get_git_head_revision(VERSION_GIT_REFSPEC VERSION_GIT_SHA1)
git_local_changes(VERSION_STATE)
git_describe(VERSION)

# ==============================================================================
# Local project configuration
# ==============================================================================
include(FrameworkConfigurationOptions)
include(ExternalProject)
include(FrameworkCoverage)

include(FrameworkSolvers)
include(FrameworkCosystems)

include(FrameworkDocumentation)

# ==============================================================================
# Targets
# ==============================================================================
add_subdirectory(lib)

add_subdirectory(framework)
add_subdirectory(exec)

if(BUILD_TESTS)
  enable_testing()
  add_subdirectory(test)
endif()
