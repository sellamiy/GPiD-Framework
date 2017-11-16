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
# ==============================================================================
set(SOLVERS_TARGETS ${SOLVERS_TARGETS} PARENT_SCOPE)
set(SOLVERS_HEADERS ${SOLVERS_HEADERS} PARENT_SCOPE)
set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} PARENT_SCOPE)
