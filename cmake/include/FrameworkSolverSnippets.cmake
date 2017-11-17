# ==============================================================================
# Solver snippets utilities
# ==============================================================================
find_package(Ruby REQUIRED)
set(SNIPPETS_GENERATOR ${CMAKE_SOURCE_DIR}/utils/snippets/SolverSnippetsGenerator.rb)
# ==============================================================================
macro(generate_solver_snippet target_directory config_directory snippet_name)
  message(STATUS "generate solver snippet ${snippet_name}")
  execute_process(COMMAND ${RUBY_EXECUTABLE} ${SNIPPETS_GENERATOR} ${ARGV})
endmacro()
# ==============================================================================
