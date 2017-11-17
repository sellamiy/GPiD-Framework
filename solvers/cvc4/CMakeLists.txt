# ==============================================================================
# CVC4 Solver Target
# ==============================================================================
find_package(CVC4)
if (NOT CVC4_FOUND)
  message(WARNING "Forcefully deactivates CVC4 interface as the Solver was not found")
else()
  include_directories(${CVC4_INCLUDE_DIR})
  # ============================================================================
  include(FrameworkSolverRegistration)
  # ============================================================================
  set(SOLVER_INTERFACE_HEADER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
  file(GLOB SOLVER_INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxx/src/*.cpp")
  register_solver_library(cvc4 ${SOLVER_INTERFACE_HEADER_DIR} ${SOLVER_INTERFACE_SOURCES})
  target_solver_libraries(cvc4 cvc4 cvc4parser)
  generate_solver_interface_header(cvc4 "gpid/solvers-wrap")
  register_solver_snippet_config(cvc4 "${CMAKE_CURRENT_SOURCE_DIR}/snippets-config.yaml")
  # ============================================================================
endif()
