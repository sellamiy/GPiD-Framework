# ==============================================================================
# Solver registration utilities
# ==============================================================================
include(FrameworkSolverSnippets)
# ==============================================================================
macro(generate_solver_interface_sources solver_name solver_snippets_dir)
  file(GLOB SNIPPETS_SOURCES
    "${solver_snippets_dir}/*.hpp"
    "${solver_snippets_dir}/*.cpp"
    "${solver_snippets_dir}/*.spp")
  set(INTERFACE_HEADERS_TARGET gpid-${solver_name}-headers)
  set(INTERFACE_SOURCES_TARGET gpid-${solver_name}-sources)

  foreach(local_snippet ${SNIPPETS_SOURCES})
    get_filename_component(local_snippet_name ${local_snippet} NAME)
    configure_file(${local_snippet}
      "${LOCAL_SOLVERS_SNIPPETS_DIR}/${solver_name}/${local_snippet_name}" COPYONLY)
  endforeach()

  set(REQUIRED_HEADER_SNIPPETS
    context.hpp inputs.hpp outputs.hpp problem.hpp engine.hpp solver.hpp)
  set(REQUIRED_SOURCE_SNIPPETS
    algorithms.cpp context.cpp problem.cpp solver.cpp parsers.cpp abducible_wrappers.cpp)

  foreach(snippet ${REQUIRED_HEADER_SNIPPETS})
    generate_solver_snippet(${LOCAL_SOLVERS_INTERFACES_HEADER_DIR}
      ${LOCAL_SOLVERS_SNIPPETS_CONFIG} ${snippet} ${solver_name})
    list(APPEND INTERFACE_HEADERS "${CURRENT_SNIPPET_OUTPUT_TARGETS}")
  endforeach()
  add_custom_target(${INTERFACE_HEADERS_TARGET} DEPENDS ${INTERFACE_HEADERS})

  foreach(snippet ${REQUIRED_SOURCE_SNIPPETS})
    generate_solver_snippet(${LOCAL_SOLVERS_INTERFACES_SOURCE_DIR}
      ${LOCAL_SOLVERS_SNIPPETS_CONFIG} ${snippet} ${solver_name})
    list(APPEND INTERFACE_SOURCES "${CURRENT_SNIPPET_OUTPUT_TARGETS}")
  endforeach()
  add_custom_target(${INTERFACE_SOURCES_TARGET} DEPENDS ${INTERFACE_SOURCES})
endmacro()
# ==============================================================================
macro(register_solver_library solver_name solver_snippets_dir)
  # ====== Define names ======
  set(INTERFACE_SOURCES "")
  set(INTERFACE_TARGET gpid-${solver_name})
  set(INTERFACE_STATIC_TARGET gpid-${solver_name}-static)
  set(INTERFACE_SHARED_TARGET gpid-${solver_name}-shared)
  # ====== Define sources targets ======
  generate_solver_interface_sources(${solver_name} ${solver_snippets_dir})
  # ====== Define libraries targets ======
  add_library(${INTERFACE_STATIC_TARGET} STATIC ${INTERFACE_SOURCES})
  add_library(${INTERFACE_SHARED_TARGET} SHARED ${INTERFACE_SOURCES})
  add_dependencies(${INTERFACE_STATIC_TARGET} ${INTERFACE_HEADERS_TARGET})
  add_dependencies(${INTERFACE_SHARED_TARGET} ${INTERFACE_HEADERS_TARGET})
  target_include_directories(${INTERFACE_STATIC_TARGET}
    PUBLIC
    "${LOCAL_SOLVERS_HEADERS_INCLUDE}"
    "${LOCAL_SOLVERS_SNIPPETS_INCLUDE}"
    "${LOCAL_SOLVERS_INTERFACES_INCLUDE}")
  target_include_directories(${INTERFACE_SHARED_TARGET}
    PUBLIC
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
  set(INTERFACE_MAIN_HEADER ${CURRENT_SNIPPET_OUTPUT_TARGETS})
  set(INTERFACE_MAIN_HEADER_TARGET gpid-solvers-headers-${solver_name})
  add_custom_target(${INTERFACE_MAIN_HEADER_TARGET} DEPENDS ${INTERFACE_MAIN_HEADER})
  add_dependencies(${INTERFACE_STATIC_TARGET} ${INTERFACE_MAIN_HEADER_TARGET})
  add_dependencies(${INTERFACE_SHARED_TARGET} ${INTERFACE_MAIN_HEADER_TARGET})
  # ====== Update solvers lists ======
  set(SOLVERS_TARGETS ${SOLVERS_TARGETS} ${solver_name} PARENT_SCOPE)
  set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} ${INTERFACE_STATIC_TARGET} PARENT_SCOPE)
  set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} ${INTERFACE_SHARED_TARGET} PARENT_SCOPE)
  set(SOLVERS_INTERFACE_TARGETS ${SOLVERS_INTERFACE_TARGETS} ${INTERFACE_MAIN_HEADER_TARGET})
  set(SOLVERS_INTERFACE_HEADERS ${SOLVERS_INTERFACE_HEADERS} ${INTERFACE_MAIN_HEADER})
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
