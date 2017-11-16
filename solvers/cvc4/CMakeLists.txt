# ==============================================================================
# CVC4 Solver Target
# ==============================================================================
find_package(CVC4)
if (NOT CVC4_FOUND)
  message(WARNING "Forcefully deactivates CVC4 interface as the Solver was not found")
  set(CVC4_SOLVER_INTERFACE OFF CACHE BOOL "Define a smt solver class based on cvc4" FORCE)
else()
  include_directories(${CVC4_INCLUDE_DIR})
endif()
# ==============================================================================
include(FrameworkSolverRegistration)
# ==============================================================================
set(SOLVER_INTERFACE_HEADER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
file(GLOB SOLVER_INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxx/src/*.cpp")
register_solver_library(cvc4 ${SOLVER_INTERFACE_HEADER_DIR} ${SOLVER_INTERFACE_SOURCES})
target_solver_libraries(cvc4 cvc4 cvc4parser)
generate_solver_interface_header(cvc4 "gpid/solvers-wrap")
# ==============================================================================
set(SOLVERS_TARGETS ${SOLVERS_TARGETS} PARENT_SCOPE)
set(SOLVERS_HEADERS ${SOLVERS_HEADERS} PARENT_SCOPE)
set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} PARENT_SCOPE)
