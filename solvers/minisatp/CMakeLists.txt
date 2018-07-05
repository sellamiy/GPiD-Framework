# ==============================================================================
# Minisat Solver Target
# ==============================================================================
find_package(ZLIB REQUIRED)

configure_file(${CMAKE_SOURCE_DIR}/cmake/modules/Minisat.cmake.in
  ${CMAKE_BINARY_DIR}/minisat-download/CMakeLists.txt)
execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/minisat-download)
if(result)
  message(FATAL_ERROR "CMake step for minisat failed: ${result}")
endif()
execute_process(COMMAND ${CMAKE_COMMAND} --build .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/minisat-download )
if(result)
  message(FATAL_ERROR "Download step for minisat failed: ${result}")
endif()

add_subdirectory(${CMAKE_BINARY_DIR}/minisat-src
  ${CMAKE_BINARY_DIR}/minisat-build
  EXCLUDE_FROM_ALL)
# ==============================================================================
include(FrameworkSolverRegistration)
# ------------------------------------------------------------------------------
file(GLOB INTERFACE_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
file(GLOB INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
# ------------------------------------------------------------------------------
include_directories("${CMAKE_BINARY_DIR}/minisat-src")
# ------------------------------------------------------------------------------
add_library(minisatp-static STATIC ${INTERFACE_SOURCES})
add_library(minisatp-shared SHARED ${INTERFACE_SOURCES})
target_include_directories(minisatp-static
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${CMAKE_BINARY_DIR}/minisat-src")
target_include_directories(minisatp-shared
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${CMAKE_BINARY_DIR}/minisat-src")
set_target_properties(minisatp-static PROPERTIES OUTPUT_NAME minisatp-interface CLEAN_DIRECT_OUTPUT 1)
set_target_properties(minisatp-shared PROPERTIES OUTPUT_NAME minisatp-interface CLEAN_DIRECT_OUTPUT 1)
target_link_libraries(minisatp-static minisat-lib-static gpid-core-static)
target_link_libraries(minisatp-shared minisat-lib-shared gpid-core-shared)
# ------------------------------------------------------------------------------
include(FrameworkSolverRegistration)
generate_interface_config_file(minisatp
  minisatp-interface.hpp MinisatInterface MinisatLiteralsGenerator)
# ------------------------------------------------------------------------------
set(LOCAL_INTERFACE_NAME minisatp PARENT_SCOPE)