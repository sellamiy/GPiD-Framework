# ==============================================================================
# z3 Solver Target
# ==============================================================================
find_package(Z3)
if (NOT Z3_FOUND)
  message(WARNING "Forcefully deactivates Z3 interface as the Solver was not found")
else()
  include_directories(${Z3_CXX_INCLUDE_DIRS})
  # ============================================================================
  include(FrameworkSolverRegistration)
  # ============================================================================
  set(SOLVER_INTERFACE_HEADER_DIR "${CMAKE_CURRENT_SOURCE_DIR}/cxx")
  file(GLOB SOLVER_INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxx/src/*.cpp")
  register_solver_snippet_config(z3 "${CMAKE_CURRENT_SOURCE_DIR}/snippets-config.yaml")
  register_solver_library(z3 ${SOLVER_INTERFACE_HEADER_DIR} ${SOLVER_INTERFACE_SOURCES})
  target_solver_libraries(z3 ${Z3_LIBRARIES})
  # ============================================================================
endif()
