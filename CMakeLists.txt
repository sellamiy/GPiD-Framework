cmake_minimum_required(VERSION 3.5)
# ========== Project Definition ==========
project(gpid-framework
  VERSION "0.0.1")
set(EXTENDED_PROJECT_NAME "GPiD Framework - Prime Implicates by Decomposition")

# ========== Project Options ==========
option(BUILD_DOC "Build documentation" ON)
option(BUILD_TESTS "Build tests" ON)
option(COVERAGE_TOOLS "Configure and compile for code coverage reports" OFF)
option(USE_COLORS "Configure color print outputs" ON)

option(MERGE_MINISAT_OUTPUT_WRAPPERS "Merge Minisat printers into its original namespace" ON)

if (COVERAGE_TOOLS AND NOT BUILD_TESTS)
  message(WARNING "Coverage targets cannot be configured if tests are not built alongside it!")
endif()

# ========== Cmake Project Global Configuration ==========
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/coverage/")
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
set(TESTS_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/test-bin)

if(USE_COLORS AND NOT WIN32)
  set(USE_ANSI_COLORS "ON")
endif()

# ========== Finding Packages ==========
include(ExternalProject)
if (COVERAGE_TOOLS)
  include(CodeCoverage)
endif()
find_package(Doxygen)

find_package(ZLIB)
include_directories(${ZLIB_INCLUDE_DIR})

# ========== Cmake Project Local Configuration ==========
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")
if (COVERAGE_TOOLS)
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/include/*" "/usr/include/c++/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/include/*/*" "/usr/include/c++/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/include/*/*/*" "/usr/include/c++/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/include/c++/*/*")
  append_coverage_compiler_flags("-Wno-inline")
endif()

set(LOCAL_LIB_HEADERS_DIR "${CMAKE_BINARY_DIR}/lib-include-local")
set(FRAMEWORK_CONF_HEADERS_DIR "${CMAKE_BINARY_DIR}/framework-include")

# ========== Files Configuration ==========
configure_file(lib/starray/starray/starray.hpp.in ${LOCAL_LIB_HEADERS_DIR}/starray/starray.hpp)

configure_file(framework/gpid/include/config.hpp.in ${FRAMEWORK_CONF_HEADERS_DIR}/gpid/config.hpp)
configure_file(framework/gpid/include/errors.hpp.in ${FRAMEWORK_CONF_HEADERS_DIR}/gpid/errors.hpp)
configure_file(framework/gpid/include/gpid.hpp.in ${FRAMEWORK_CONF_HEADERS_DIR}/gpid/gpid.hpp)

# ========== Minisat ==========
file(GLOB MINISAT_PATCHES "cmake/minisat/*.patch")
ExternalProject_Add(minisat-solver
  GIT_REPOSITORY    https://github.com/niklasso/minisat.git
  GIT_TAG           37dc6c67e2af26379d88ce349eb9c4c6160e8543
  SOURCE_DIR        "${CMAKE_BINARY_DIR}/minisat-src"
  BINARY_DIR        "${CMAKE_BINARY_DIR}/minisat-build"
  CMAKE_ARGS        -DCMAKE_CXX_STANDARD=${CMAKE_CXX_STANDARD} -Wno-dev
  PATCH_COMMAND     git apply ${MINISAT_PATCHES}
  INSTALL_COMMAND   ""
  TEST_COMMAND      ""
  )
add_library(minisat-lib-shared SHARED IMPORTED)
add_dependencies(minisat-lib-shared minisat-solver)
if(WIN32)
  set_property(TARGET minisat-lib-shared PROPERTY IMPORTED_LOCATION
    ${CMAKE_BINARY_DIR}/minisat-build/minisat.dll)
elseif(APPLE)
  set_property(TARGET minisat-lib-shared PROPERTY IMPORTED_LOCATION
    ${CMAKE_BINARY_DIR}/minisat-build/libminisat.dylib)
else()
  set_property(TARGET minisat-lib-shared PROPERTY IMPORTED_LOCATION
    ${CMAKE_BINARY_DIR}/minisat-build/libminisat.so)
endif()
include_directories("${CMAKE_BINARY_DIR}/minisat-src")

if (COVERAGE_TOOLS)
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/minisat-src/minisat/*/*")
endif()

# ========== Local Libraries Dependencies ==========
include_directories("${LOCAL_LIB_HEADERS_DIR}")

# ========== Headers ==========
include_directories("lib/starray")

include_directories("${FRAMEWORK_CONF_HEADERS_DIR}")
include_directories("framework")

# ========== Source Files ==========
file(GLOB LIBSTARRAY_SOURCES "lib/starray/src/*.cpp")

file(GLOB LIBGPID_SOURCES "framework/src/*/*.cpp")

# ========== Libraries Targets ==========
add_library(starray SHARED ${LIBSTARRAY_SOURCES})

add_library(gpid SHARED ${LIBGPID_SOURCES})
target_link_libraries(gpid starray)
target_link_libraries(gpid minisat-lib-shared)
target_link_libraries(gpid ${ZLIB_LIBRARY})

# ========== Example Programs Targets ==========
add_executable(gpid-prop "example/gpid-prop.cpp")
target_link_libraries(gpid-prop gpid)

# ========== Tests ==========

if(BUILD_TESTS)

  # ===== Configuring Test Framework =====

  enable_testing()

  # Download and unpack googletest at configure time
  configure_file(cmake/googletest/CMakeLists.txt.in googletest-download/CMakeLists.txt)
  execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
  if(result)
    message(FATAL_ERROR "CMake step for googletest failed: ${result}")
  endif()
  execute_process(COMMAND ${CMAKE_COMMAND} --build .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
  if(result)
    message(FATAL_ERROR "Build step for googletest failed: ${result}")
  endif()

  # Prevent overriding the parent project's compiler/linker
  # settings on Windows
  set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)

  # Add googletest directly to our build. This defines
  # the gtest and gtest_main targets.
  add_subdirectory(${CMAKE_BINARY_DIR}/googletest-src
    ${CMAKE_BINARY_DIR}/googletest-build)

  # The gtest/gtest_main targets carry header search path
  # dependencies automatically when using CMake 2.8.11 or
  # later. Otherwise we have to add them here ourselves.
  if (CMAKE_VERSION VERSION_LESS 2.8.11)
    include_directories("${gtest_SOURCE_DIR}/include")
  endif()

  # ===== Generating Test Targets =====

  file(GLOB LIB_TEST_FILES "test/lib/starray/*.cpp")
  foreach(filename ${LIB_TEST_FILES})
    # message(STATUS "Configuring testfile: ${filename}")
    get_filename_component(execname "${filename}" NAME_WE)
    add_executable(${execname} "${filename}")
    target_link_libraries(${execname} starray)
    target_link_libraries(${execname} gtest gtest_main)
    set_target_properties(${execname} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${TESTS_RUNTIME_OUTPUT_DIRECTORY})
    add_test(NAME ${execname} COMMAND ${execname})
  endforeach()

  # ===== Coverage =====

  if (COVERAGE_TOOLS)
    set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*")
    set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*/*")
    set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*/*/*")
    set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_SOURCE_DIR}/test/lib/*/*")
    setup_target_for_coverage(NAME coverage EXECUTABLE ctest)
  endif()

endif()

# ========== Documentation ==========

if(DOXYGEN_FOUND)

  set(DOXYGEN_INF ${CMAKE_CURRENT_SOURCE_DIR}/config/doxygen.cfg.in)
  set(DOXYGEN_OUTF ${CMAKE_CURRENT_BINARY_DIR}/doxygen.cfg)

  if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    message(STATUS "Doxygen: Set to debug mode documentation")
    set(DOCUMENT_HIDDEN_ELEMENTS "YES")
  else()
    message(STATUS "Doxygen: Set to release mode documentation")
    set(DOCUMENT_HIDDEN_ELEMENTS "NO")
  endif()

  if(DOXYGEN_DOT_FOUND)
    set(DOXYGEN_HAVE_DOT_PARAM "YES")
    message(STATUS "Doxygen: Enable dot graph generation")
  else()
    set(DOXYGEN_HAVE_DOT_PARAM "NO")
    message(STATUS "Doxygen: Disable dot graph generation")
  endif()

  configure_file(${DOXYGEN_INF} ${DOXYGEN_OUTF} @ONLY)

  add_custom_target(doc
    COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUTF}
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    COMMENT "Doxygen: Generating API documentation"
    VERBATIM)

else()
  message(WARNING "Doxygen was not found. No documentation generated.")
endif()
