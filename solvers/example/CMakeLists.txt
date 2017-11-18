# ==============================================================================
# True Solver Target
# ==============================================================================
include(FrameworkSolverRegistration)
# ==============================================================================
set(SOLVER_INTERFACE_HEADER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
file(GLOB SOLVER_INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxx/src/*.cpp")
register_solver_library(truesolver ${SOLVER_INTERFACE_HEADER_DIR} ${SOLVER_INTERFACE_SOURCES})
register_solver_snippet_config(truesolver "${CMAKE_CURRENT_SOURCE_DIR}/snippets-config.yaml")
# ==============================================================================
