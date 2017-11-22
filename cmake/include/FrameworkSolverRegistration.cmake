# ==============================================================================
# Solver registration utilities
# ==============================================================================
include(FrameworkSolverSnippets)
# ==============================================================================
macro(register_solver_library solver_name solver_includes)
  # ====== Define names ======
  set(INTERFACE_SOURCES ${ARGN})
  set(INTERFACE_TARGET gpid-${solver_name})
  set(INTERFACE_STATIC_TARGET gpid-${solver_name}-static)
  set(INTERFACE_SHARED_TARGET gpid-${solver_name}-shared)
  # ====== Define libraries targets ======
  add_library(${INTERFACE_STATIC_TARGET} STATIC ${INTERFACE_SOURCES})
  add_library(${INTERFACE_SHARED_TARGET} SHARED ${INTERFACE_SOURCES})
  target_include_directories(${INTERFACE_STATIC_TARGET}
    PUBLIC "${solver_includes}"
    "${LOCAL_SOLVERS_HEADERS_INCLUDE}"
    "${LOCAL_SOLVERS_SNIPPETS_INCLUDE}"
    "${LOCAL_SOLVERS_INTERFACES_INCLUDE}")
  target_include_directories(${INTERFACE_SHARED_TARGET}
    PUBLIC "${solver_includes}"
    "${LOCAL_SOLVERS_HEADERS_INCLUDE}"
    "${LOCAL_SOLVERS_SNIPPETS_INCLUDE}"
    "${LOCAL_SOLVERS_INTERFACES_INCLUDE}")
  set_target_properties(${INTERFACE_STATIC_TARGET} PROPERTIES
    OUTPUT_NAME ${INTERFACE_TARGET}
    CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(${INTERFACE_SHARED_TARGET} PROPERTIES
    OUTPUT_NAME ${INTERFACE_TARGET}
    VERSION ${VERSION}
    CLEAN_DIRECT_OUTPUT 1)
  # ====== Link to the core library ======
  target_link_libraries(${INTERFACE_STATIC_TARGET} gpid-core-static)
  target_link_libraries(${INTERFACE_SHARED_TARGET} gpid-core-shared)
  # ====== Add solver interface header target ======
  generate_solver_snippet(${LOCAL_SOLVERS_HEADERS_DIR}
    ${LOCAL_SOLVERS_SNIPPETS_CONFIG} interface.hpp ${solver_name})
  set(INTERFACE_HEADERS ${CURRENT_SNIPPET_OUTPUT_TARGETS})
  set(INTERFACE_HEADERS_TARGET gpid-solvers-headers-${solver_name})
  add_custom_target(${INTERFACE_HEADERS_TARGET} DEPENDS ${INTERFACE_HEADERS})
  add_dependencies(${INTERFACE_STATIC_TARGET} ${INTERFACE_HEADERS_TARGET})
  add_dependencies(${INTERFACE_SHARED_TARGET} ${INTERFACE_HEADERS_TARGET})
  # ====== Update solvers lists ======
  set(SOLVERS_TARGETS ${SOLVERS_TARGETS} ${solver_name} PARENT_SCOPE)
  set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} ${INTERFACE_STATIC_TARGET} PARENT_SCOPE)
  set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} ${INTERFACE_SHARED_TARGET} PARENT_SCOPE)
  set(SOLVERS_INTERFACE_TARGETS ${SOLVERS_INTERFACE_TARGETS} ${INTERFACE_HEADERS_TARGET})
  set(SOLVERS_INTERFACE_HEADERS ${SOLVERS_INTERFACE_HEADERS} ${INTERFACE_HEADERS})
endmacro()
# ==============================================================================
macro(target_solver_static_libraries solver_name)
  set(INTERFACE_STATIC_TARGET gpid-${solver_name}-static)
  target_link_libraries(${INTERFACE_STATIC_TARGET} ${ARGN})
endmacro()
macro(target_solver_shared_libraries solver_name)
  set(INTERFACE_SHARED_TARGET gpid-${solver_name}-shared)
  target_link_libraries(${INTERFACE_SHARED_TARGET} ${ARGN})
endmacro()
macro(target_solver_libraries solver_name)
  target_solver_static_libraries(${ARGV})
  target_solver_shared_libraries(${ARGV})
endmacro()
# ==============================================================================
macro(target_solver_include_directories solver_name)
  set(INTERFACE_STATIC_TARGET gpid-${solver_name}-static)
  set(INTERFACE_SHARED_TARGET gpid-${solver_name}-shared)
  target_include_directories(${INTERFACE_STATIC_TARGET}
    PUBLIC "${ARGN}")
  target_include_directories(${INTERFACE_SHARED_TARGET}
    PUBLIC "${ARGN}")
endmacro()
# ==============================================================================
macro(register_solver_snippet_config solver_name config_file)
  configure_file(${config_file}
    ${LOCAL_SOLVERS_SNIPPETS_CONFIG}/${solver_name}.yaml
    COPYONLY)
endmacro()
# ==============================================================================
