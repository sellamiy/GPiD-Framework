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
set(CODEGEN_CONFIG_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/config-interface.py")
# ==============================================================================
function(generate_multi_file target_file template_file) # ARGN: interfaces_list
  set(INTERFACE_CONFIG_FILES)
  set(INTERFACE_CLI_OPTIONS)
  foreach(interface_id ${ARGN})
    list(APPEND INTERFACE_CONFIG_FILES ${interface_id}-config-file)
    list(APPEND INTERFACE_CLI_OPTIONS "--interface=${LOCAL_SOLVER_INTERFACES_CONFIGS}/${interface_id}.yml")
  endforeach()
  add_custom_command(
    OUTPUT "${target_file}"
    DEPENDS "${CODEGEN_MULTI_SCRIPT}" "${template_file}" ${INTERFACE_CONFIG_FILES}
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_MULTI_SCRIPT}"
    "--source=${template_file}" "--output=${target_file}" "--process"
    ${INTERFACE_CLI_OPTIONS})
endfunction()
# ------------------------------------------------------------------------------
function(generate_interface_config_file name header classname generationclass)
  set(INTERFACE_CONFIG_FILE "${LOCAL_SOLVER_INTERFACES_CONFIGS}/${name}.yml")
  add_custom_command(
    OUTPUT "${INTERFACE_CONFIG_FILE}"
    DEPENDS "${CODEGEN_CONFIG_SCRIPT}"
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_CONFIG_SCRIPT}"
    "--interface=${name}" "--output=${INTERFACE_CONFIG_FILE}"
    "--mainheader=\"${header}\"" "--classname=${classname}"
    "--generationclass=${generationclass}"
    "--generate")
  add_custom_target(${name}-config-file
    DEPENDS "${INTERFACE_CONFIG_FILE}" "${CODEGEN_CONFIG_SCRIPT}")
endfunction()
# ==============================================================================
function(load_interface_directory name)
  add_subdirectory(${name})
  # The previous call should set the following variables: LOCAL_INTERFACE_NAME
  # This variable should contain the base name of the interface.
  # This interface static library must be called ${LOCAL_INTERFACE_NAME}-static
  # This interface shared library must be called ${LOCAL_INTERFACE_NAME}-shared
  # It should also call generate_interface_config_file with the correct parameters
  #  to create the target for generating the ${LOCAL_INTERFACE_NAME}.yml
  #  interface configuration file.
  if ("${LOCAL_INTERFACE_NAME}" EQUAL "")
    message(WARNING "Directory ${name} did not provide an interface variable!")
  else()
    list(APPEND SOLVER_TARGETS ${LOCAL_INTERFACE_NAME})
    set(SOLVER_TARGETS ${SOLVER_TARGETS} PARENT_SCOPE)
  endif()
endfunction()
# ==============================================================================
