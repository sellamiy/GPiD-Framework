# ==============================================================================
# Ilinva registration utilities
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_python_module(colorama REQUIRED)
find_python_module(yaml REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(CODEGEN_MULTI_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/multi-ich.py")
set(CODEGEN_CONFIG_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/config-ich.py")
# ==============================================================================
function(generate_ich_multi_file)
  set(options)
  set(oneValueArgs TARGET TEMPLATE)
  set(multiValueArgs ICHANDLERS)
  cmake_parse_arguments(ICHD "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
  set(ICH_CONFIG_FILES)
  set(ICH_CLI_OPTIONS)
  foreach(ich_id ${ICHD_ICHANDLERS})
    list(APPEND ICH_CONFIG_TARGETS ${ich_id}-config-file)
    list(APPEND ICH_CONFIG_FILES "${LOCAL_ICH_CONFIGS}/${ich_id}.yml")
    list(APPEND ICH_CLI_OPTIONS "--code-handler=${LOCAL_ICH_CONFIGS}/${ich_id}.yml")
  endforeach()
  add_custom_command(
    OUTPUT "${ICHD_TARGET}"
    DEPENDS "${CODEGEN_MULTI_SCRIPT}" "${ICHD_TEMPLATE}" ${ICH_CONFIG_FILES}
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_MULTI_SCRIPT}"
    "--source=${ICHD_TEMPLATE}" "--output=${ICHD_TARGET}" "--process"
    ${ICH_CLI_OPTIONS})
  get_filename_component(template_name "${ICHD_TEMPLATE}" NAME_WE)
  add_custom_target(${template_name}-multi
    DEPENDS "${ICHD_TARGET}" "${CODEGEN_MULTI_SCRIPT}" "${ICHD_TEMPLATE}" ${ICH_CONFIG_TARGETS})
endfunction()
# ------------------------------------------------------------------------------
function(generate_ich_config_file)
  set(options)
  set(oneValueArgs NAME HEADER CONVERTERS CLASSNAME)
  set(multiValueArgs INTERFACES EXCEPTIONS)
  cmake_parse_arguments(ICHD "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
  set(ICH_CONFIG_FILE "${LOCAL_ICH_CONFIGS}/${ICHD_NAME}.yml")
  set(ICH_ADDITIONAL_CLIS)
  foreach(ich_interface ${ICHD_INTERFACES})
    list(APPEND ICH_ADDITIONAL_CLIS "--interface=${LOCAL_SOLVER_INTERFACES_CONFIGS}/${ich_interface}.yml")
  endforeach()
  foreach(ich_exception ${ICHD_EXCEPTIONS})
    list(APPEND ICH_ADDITIONAL_CLIS "--exception=\"${ich_exception}\"")
  endforeach()
  add_custom_command(
    OUTPUT "${ICH_CONFIG_FILE}"
    DEPENDS "${CODEGEN_CONFIG_SCRIPT}"
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_CONFIG_SCRIPT}"
    "--code-handler=${ICHD_NAME}" "--output=${ICH_CONFIG_FILE}"
    "--mainheader=\"${ICHD_HEADER}\"" "--classname=${ICHD_CLASSNAME}"
    "--converters=\"${ICHD_CONVERTERS}\""
    ${ICH_ADDITIONAL_CLIS} "--generate")
  add_custom_target(${ICHD_NAME}-config-file
    DEPENDS "${ICH_CONFIG_FILE}" "${CODEGEN_CONFIG_SCRIPT}")
endfunction()
# ==============================================================================
function(load_ich_directory name)
  add_subdirectory(${name})
  # The previous call should set the following variables: LOCAL_ICH_NAME
  # This variable should contain the base name of the code handler.
  # This code handler static library must be called ${LOCAL_ICH_NAME}-static
  # This code handler shared library must be called ${LOCAL_ICH_NAME}-shared
  # It should also call generate_ich_config_file with the correct parameters
  #  to create the target for generating the ${LOCAL_ICH_NAME}.yml
  #  ich configuration file.
  if ("${LOCAL_ICH_NAME}" EQUAL "")
    message(WARNING "Directory ${name} did not provide an code-handler variable!")
  else()
    list(APPEND ICH_TARGETS ${LOCAL_ICH_NAME})
    set(ICH_TARGETS ${ICH_TARGETS} PARENT_SCOPE)
  endif()
endfunction()
# ==============================================================================
