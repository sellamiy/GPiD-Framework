cmake_minimum_required(VERSION 3.5)
# ========== Project Definition ==========
project(gpid-framework
  VERSION "0.0.1")
set(EXTENDED_PROJECT_NAME "GPiD Framework - Prime Implicates by Decomposition")

# ========== Cmake Project Global Configuration ==========
set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")
set(CMAKE_CXX_STANDARD 11)

# ========== Project Options ==========
option(BUILD_DOC "Build documentation" ON)
option(BUILD_TESTS "Build tests" ON)

# ========== Finding Packages ==========
find_package(Doxygen)

# ========== Files Configuration ==========

# ========== Header Files ==========
include_directories("framework/gpid/include")

# ========== Source Files ==========
file(GLOB LIBGPID_SOURCES "framework/gpid/src/*.cpp")

# ========== Libraries Targets ==========
add_library(gpid STATIC ${LIBGPID_SOURCES})

# ========== Example Programs Targets ==========
#add_executable(example "examples/example.cpp")
#target_link_libraries(example gpid)

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

  #file(GLOB _TEST_FILES "test/*.cpp")
  #foreach(filename ${_TEST_FILES})
  #  message(STATUS "Configuring testfile: ${filename}")
  #  get_filename_component(execname "${filename}" NAME_WE)
  #  add_executable(${execname} "${filename}")
  #  target_link_libraries(${execname} gpid)
  #  target_link_libraries(${execname} gtest gtest_main)
  #  add_test(${execname} ${execname})
  #endforeach()

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
