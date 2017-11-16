# ==============================================================================
# True Solver Target
# ==============================================================================
include(FrameworkSolverRegistration)
# ==============================================================================
set(SOLVER_INTERFACE_HEADER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
file(GLOB SOLVER_INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxx/src/*.cpp")
register_solver_library(truesolver ${SOLVER_INTERFACE_HEADER_DIR} ${SOLVER_INTERFACE_SOURCES})
generate_solver_interface_header(truesolver "gpid/solvers-wrap")
# ==============================================================================
set(SOLVERS_TARGETS ${SOLVERS_TARGETS} PARENT_SCOPE)
set(SOLVERS_HEADERS ${SOLVERS_HEADERS} PARENT_SCOPE)
set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} PARENT_SCOPE)
