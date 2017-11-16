# ==============================================================================
# GPiD Target solvers
# ==============================================================================
include(FrameworkSolverRegistration)
# ==============================================================================
add_subdirectory(example)
add_subdirectory(minisat)
add_subdirectory(cvc4)
add_subdirectory(z3)
# ==============================================================================
add_library(gpid-solvers-static INTERFACE)
add_library(gpid-solvers-shared INTERFACE)
target_link_libraries(gpid-solvers-static INTERFACE ${SOLVERS_STATIC_TARGETS})
target_link_libraries(gpid-solvers-shared INTERFACE ${SOLVERS_SHARED_TARGETS})
generate_solver_interfaces_global_header()
# ==============================================================================
set(SOLVERS_TARGETS ${SOLVERS_TARGETS} PARENT_SCOPE)
set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} PARENT_SCOPE)
