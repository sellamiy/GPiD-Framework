# ==============================================================================
# Solvers finder and configuration
# ==============================================================================
# Minisat
# ==============================================================================
if (MINISAT_SOLVER_INTERFACE)
  find_package(ZLIB REQUIRED)
  include_directories(${ZLIB_INCLUDE_DIR})

  configure_file(cmake/modules/Minisat.cmake.in minisat-download/CMakeLists.txt)
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

  add_subdirectory(${CMAKE_BINARY_DIR}/minisat-src EXCLUDE_FROM_ALL)
  include_directories(${CMAKE_BINARY_DIR}/minisat-src)
endif()
# ==============================================================================
# CVC4
# ==============================================================================
if (CVC4_SOLVER_INTERFACE)
  find_package(CVC4)
  if (NOT CVC4_FOUND)
    message(WARNING "Forcefully deactivates CVC4 interface as the Solver was not found")
    set(CVC4_SOLVER_INTERFACE OFF CACHE BOOL "Define a smt solver class based on cvc4" FORCE)
  else()
    include_directories(${CVC4_INCLUDE_DIR})
  endif()
endif()
# ==============================================================================
# Z3
# ==============================================================================
if (Z3_SOLVER_INTERFACE)
  find_package(Z3)
  if (NOT Z3_FOUND)
    message(WARNING "Forcefully deactivates Z3 interface as the Solver was not found")
    set(Z3_SOLVER_INTERFACE OFF CACHE BOOL "Define a smt solver class based on z3" FORCE)
  else()
    include_directories(${Z3_CXX_INCLUDE_DIRS})
  endif()
endif()
