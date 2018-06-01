# ==============================================================================
# Solver registration utilities
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_python_module(colorama REQUIRED)
find_python_module(yaml REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(CODEGEN_MULTI_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/multi-interface.py")
set(CODEGEN_SINGLE_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/single-interface.py")
# ==============================================================================
macro(set_interface_targets_names interface_name)
  set(INTERFACE_TARGET gpid-${interface_name}-si)
  set(INTERFACE_STATIC_TARGET gpid-${interface_name}-si-static)
  set(INTERFACE_SHARED_TARGET gpid-${interface_name}-si-shared)
endmacro()
# ------------------------------------------------------------------------------
macro(set_interface_subtargets_names interface_name)
  set(INTERFACE_HEADERS_TARGET gpid-${interface_name}-si-headers)
  set(INTERFACE_SOURCES_TARGET gpid-${interface_name}-si-sources)
  set(INTERFACE_MAIN_HEADER_TARGET gpid-${interface_name}-si-main-header)
endmacro()
# ==============================================================================
function(generate_multi_file target_file template_file) # ARGN: interfaces_list
  set(INTERFACE_CONFIG_FILES)
  set(INTERFACE_CLI_OPTIONS)
  foreach(interface_id ${ARGN})
    list(APPEND INTERFACE_CONFIG_FILES "${LOCAL_SOLVER_INTERFACES_CONFIGS}/${interface_id}.yml")
    list(APPEND INTERFACE_CLI_OPTIONS "--interface=${LOCAL_SOLVER_INTERFACES_CONFIGS}/${interface_id}.yml")
  endforeach()
  add_custom_command(
    OUTPUT "${target_file}"
    DEPENDS "${CODEGEN_MULTI_SCRIPT}" "${template_file}"
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_MULTI_SCRIPT}" ${INTERFACE_CONFIG_FILES}
    "--source=${template_file}" "--output=${target_file}" "--process"
    ${INTERFACE_CLI_OPTIONS})
endfunction()
# ------------------------------------------------------------------------------
function(generate_single_file)
  # TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO #
endfunction()
# ==============================================================================
# TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO =v=
# TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO =v=
# TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO =v=
# TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO =v=
# TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO =v=
# TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO TODO =v=
# ==============================================================================
macro(register_solver_interface interface_name)
  # ==== Define targets ====
  set_interface_targets_names(${interface_name})
  set_interface_subtargets_names(${interface_name})
  # ==== Recover headers and sources ====
  add_custom_target(${INTERFACE_HEADERS_TARGET}
    DEPENDS ${SOLVER_INTERFACE_PREPROCESSED_HEADERS})
  add_custom_target(${INTERFACE_SOURCES_TARGET}
    DEPENDS ${SOLVER_INTERFACE_PREPROCESSED_SOURCES})
  # ==== Link librairies ====
  add_library(${INTERFACE_STATIC_TARGET} STATIC ${INTERFACE_SOURCES})
  add_library(${INTERFACE_SHARED_TARGET} SHARED ${INTERFACE_SOURCES})
  add_dependencies(${INTERFACE_STATIC_TARGET} ${INTERFACE_HEADERS_TARGET})
  add_dependencies(${INTERFACE_SHARED_TARGET} ${INTERFACE_HEADERS_TARGET})
  target_include_directories(${INTERFACE_STATIC_TARGET}
    PUBLIC "${SOLVER_INTERFACES_INCLUDE_DIR}/${interface_name}")
  target_include_directories(${INTERFACE_SHARED_TARGET}
    PUBLIC "${SOLVER_INTERFACES_INCLUDE_DIR}/${interface_name}")
  set_target_properties(${INTERFACE_STATIC_TARGET} PROPERTIES
    OUTPUT_NAME ${INTERFACE_TARGET}
    VERSION ${VERSION}
    CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(${INTERFACE_SHARED_TARGET} PROPERTIES
    OUTPUT_NAME ${INTERFACE_TARGET}
    VERSION ${VERSION}
    CLEAN_DIRECT_OUTPUT 1)
  # ==== Link to the core library ====
  target_link_libraries(${INTERFACE_STATIC_TARGET} gpid-core-static)
  target_link_libraries(${INTERFACE_SHARED_TARGET} gpid-core-shared)
  # ==== Add solver interface main header target ====
  add_custom_target(${INTERFACE_MAIN_HEADER_TARGET} DEPENDS ${SOLVER_INTERFACE_MAIN_HEADER})
  add_dependencies(${INTERFACE_STATIC_TARGET} ${INTERFACE_MAIN_HEADER_TARGET})
  add_dependencies(${INTERFACE_SHARED_TARGET} ${INTERFACE_MAIN_HEADER_TARGET})
  # ==== Update solvers lists ====
  set(SOLVER_TARGETS ${SOLVER_TARGETS} ${interface_name} PARENT_SCOPE)
  set(SOLVER_STATIC_TARGETS ${SOLVER_STATIC_TARGETS} ${INTERFACE_STATIC_TARGET} PARENT_SCOPE)
  set(SOLVER_SHARED_TARGETS ${SOLVER_SHARED_TARGETS} ${INTERFACE_SHARED_TARGET} PARENT_SCOPE)
  set(SOLVER_INTERFACE_TARGETS ${SOLVER_INTERFACE_TARGETS} ${INTERFACE_MAIN_HEADER_TARGET})
  set(SOLVER_INTERFACE_HEADERS ${SOLVER_INTERFACE_HEADERS} ${INTERFACE_MAIN_HEADER})
endmacro()
# ------------------------------------------------------------------------------
macro(solver_interface_target_include_directories interface_name)
  set_interface_targets_names(${interface_name})
  target_include_directories(${INTERFACE_STATIC_TARGET}
    PUBLIC "${ARGN}")
  target_include_directories(${INTERFACE_SHARED_TARGET}
    PUBLIC "${ARGN}")
endmacro()
# ------------------------------------------------------------------------------
macro(solver_interface_target_libraries interface_name)
  set_interface_targets_names(${interface_name})
  target_link_libraries(${INTERFACE_STATIC_TARGET} ${ARGN})
  target_link_libraries(${INTERFACE_SHARED_TARGET} ${ARGN})
endmacro()
# ==============================================================================
