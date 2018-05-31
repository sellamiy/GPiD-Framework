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
# ==============================================================================
set(SOLVER_INTERFACE_HEADER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
file(GLOB SOLVER_INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxx/src/*.cpp")
register_solver_snippet_config(minisat "${CMAKE_CURRENT_SOURCE_DIR}/snippets-config.yaml")
register_solver_library(minisat ${SOLVER_INTERFACE_HEADER_DIR} ${SOLVER_INTERFACE_SOURCES})
target_solver_include_directories(minisat "${CMAKE_BINARY_DIR}/minisat-src")
target_solver_static_libraries(minisat minisat-lib-static)
target_solver_shared_libraries(minisat minisat-lib-shared)
# ==============================================================================
