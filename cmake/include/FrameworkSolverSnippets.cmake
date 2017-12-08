# ==============================================================================
# Solver snippets utilities
# ==============================================================================
find_package(Ruby REQUIRED)
set(SNIPPETS_GENERATOR ${CMAKE_SOURCE_DIR}/utils/snippets/SolverSnippetsGenerator.rb)
set(SNIPPETS_TEMPLATES_LOCATION "${CMAKE_SOURCE_DIR}/framework/templates")
# ==============================================================================
macro(generate_solver_snippet target_directory config_directory snippet_name)
  set(SNIPPET_AS_SINGLE_PATH
    "${SNIPPETS_TEMPLATES_LOCATION}/single/${snippet_name}.erb")
  set(SNIPPET_AS_MULTI_PATH
    "${SNIPPETS_TEMPLATES_LOCATION}/multi/${snippet_name}.erb")
  set(CURRENT_SNIPPET_DEPENDS_TARGETS ${SNIPPETS_GENERATOR})
  foreach(solver_name ${ARGN})
    list(APPEND CURRENT_SNIPPET_DEPENDS_TARGETS
      "${config_directory}/${solver_name}.yaml")
  endforeach()

  if(EXISTS "${SNIPPET_AS_SINGLE_PATH}")
    set(CURRENT_SNIPPET_OUTPUT_TARGETS "")
    foreach(solver_name ${ARGN})
      list(APPEND CURRENT_SNIPPET_OUTPUT_TARGETS
	"${target_directory}/${solver_name}_${snippet_name}")
      add_custom_command(
	OUTPUT "${target_directory}/${solver_name}_${snippet_name}"
	DEPENDS ${SNIPPET_AS_SINGLE_PATH}
	"${config_directory}/${solver_name}.yaml"
	COMMAND ${RUBY_EXECUTABLE} ${SNIPPETS_GENERATOR} ${SNIPPETS_TEMPLATES_LOCATION}
	${target_directory} ${config_directory} ${snippet_name} ${solver_name})
    endforeach()

  elseif(EXISTS "${SNIPPET_AS_MULTI_PATH}")
    list(APPEND CURRENT_SNIPPET_DEPENDS_TARGETS ${SNIPPET_AS_MULTI_PATH})
    set(CURRENT_SNIPPET_OUTPUT_TARGETS
      "${target_directory}/${snippet_name}")
    add_custom_command(
      OUTPUT "${target_directory}/${snippet_name}"
      DEPENDS ${CURRENT_SNIPPET_DEPENDS_TARGETS}
      COMMAND ${RUBY_EXECUTABLE} ${SNIPPETS_GENERATOR} ${SNIPPETS_TEMPLATES_LOCATION} ${ARGV})

  else()
    message(ERROR "Unknown solver snippet: ${snippet_name}")
  endif()

endmacro()
# ==============================================================================
