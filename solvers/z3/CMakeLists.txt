# ==============================================================================
# z3 Solver Target
# ==============================================================================
find_package(Z3)
if (NOT Z3_FOUND)
  message(WARNING "Forcefully deactivates Z3 interface as the Solver was not found")
  set(Z3_SOLVER_INTERFACE OFF CACHE BOOL "Define a smt solver class based on z3" FORCE)
else()
  include_directories(${Z3_CXX_INCLUDE_DIRS})
endif()
# ==============================================================================
include(FrameworkSolverRegistration)
# ==============================================================================
set(SOLVER_INTERFACE_HEADER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
file(GLOB SOLVER_INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxx/src/*.cpp")
register_solver_library(z3 ${SOLVER_INTERFACE_HEADER_DIR} ${SOLVER_INTERFACE_SOURCES})
target_solver_libraries(z3 ${Z3_LIBRARIES})
generate_solver_interface_header(z3 "gpid/solvers-wrap")
register_solver_snippet_config(z3 "${CMAKE_CURRENT_SOURCE_DIR}/snippets-config.yaml")
# ==============================================================================
