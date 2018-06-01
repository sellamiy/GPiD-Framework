# ==============================================================================
# CVC4 Solver Target
# ==============================================================================
find_package(CVC4)
if (NOT CVC4_FOUND)
  message(WARNING "Forcefully deactivates CVC4 interface as the Solver was not found")
else()
  # ============================================================================
  include(FrameworkSolverRegistration)
  # ============================================================================
  set(SOLVER_INTERFACE_SNIPPETS_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
  register_solver_snippet_config(cvc4 "${CMAKE_CURRENT_SOURCE_DIR}/snippets-config.yaml")
  register_solver_library(cvc4 ${SOLVER_INTERFACE_SNIPPETS_DIR})
  target_solver_include_directories(cvc4 ${CVC4_INCLUDE_DIR})
  target_solver_libraries(cvc4 cvc4 cvc4parser)
  # ============================================================================
endif()
