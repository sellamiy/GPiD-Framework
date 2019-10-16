# ==============================================================================
# Minpart context registration utilities
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_python_module(colorama REQUIRED)
find_python_module(yaml REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(CODEGEN_MULTI_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/multi-mpcontext.py")
set(CODEGEN_CONFIG_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/config-mpcontext.py")
# ==============================================================================
function(generate_mpcontext_multi_file)
  set(options)
  set(oneValueArgs TARGET TEMPLATE)
  set(multiValueArgs MPCONTEXT)
  cmake_parse_arguments(MPCONTEXTD "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
  set(MPCONTEXT_CONFIG_FILES)
  set(MPCONTEXT_CLI_OPTIONS)
  foreach(mpcontext_id ${MPCONTEXTD_MPCONTEXT})
    list(APPEND MPCONTEXT_CONFIG_TARGETS ${mpcontext_id}-config-file)
    list(APPEND MPCONTEXT_CONFIG_FILES "${LOCAL_MPCONTEXT_CONFIGS}/${mpcontext_id}.yml")
    list(APPEND MPCONTEXT_CLI_OPTIONS "--context=${LOCAL_MPCONTEXT_CONFIGS}/${mpcontext_id}.yml")
  endforeach()
  add_custom_command(
    OUTPUT "${MPCONTEXTD_TARGET}"
    DEPENDS "${CODEGEN_MULTI_SCRIPT}" "${MPCONTEXTD_TEMPLATE}" ${MPCONTEXT_CONFIG_FILES}
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_MULTI_SCRIPT}"
    "--source=${MPCONTEXTD_TEMPLATE}" "--output=${MPCONTEXTD_TARGET}" "--process"
    ${MPCONTEXT_CLI_OPTIONS})
  get_filename_component(template_name "${MPCONTEXTD_TEMPLATE}" NAME_WE)
  add_custom_target(${template_name}-multi
    DEPENDS "${MPCONTEXTD_TARGET}" "${CODEGEN_MULTI_SCRIPT}" "${MPCONTEXTD_TEMPLATE}" ${MPCONTEXT_CONFIG_TARGETS})
endfunction()
# ------------------------------------------------------------------------------
function(generate_mpcontext_config_file)
  set(options)
  set(oneValueArgs NAME HEADER CONVERTERS CLASSNAME OPTCLASSNAME)
  cmake_parse_arguments(MPCONTEXTD "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
  set(MPCONTEXT_CONFIG_FILE "${LOCAL_MPCONTEXT_CONFIGS}/${MPCONTEXTD_NAME}.yml")
  set(MPCONTEXT_ADDITIONAL_CLIS)
  add_custom_command(
    OUTPUT "${MPCONTEXT_CONFIG_FILE}"
    DEPENDS "${CODEGEN_CONFIG_SCRIPT}"
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_CONFIG_SCRIPT}"
    "--context=${MPCONTEXTD_NAME}" "--output=${MPCONTEXT_CONFIG_FILE}"
    "--mainheader=\"${MPCONTEXTD_HEADER}\"" "--classname=${MPCONTEXTD_CLASSNAME}"
    "--optclassname=${MPCONTEXTD_OPTCLASSNAME}"
    ${MPCONTEXT_ADDITIONAL_CLIS} "--generate")
  add_custom_target(${MPCONTEXTD_NAME}-config-file
    DEPENDS "${MPCONTEXT_CONFIG_FILE}" "${CODEGEN_CONFIG_SCRIPT}")
endfunction()
# ==============================================================================
function(load_mpcontext_directory name)
  add_subdirectory(${name})
  # The previous call should set the following variables: LOCAL_MPCONTEXT_NAME
  # This variable should contain the base name of the code handler.
  # This code handler static library must be called ${LOCAL_MPCONTEXT_NAME}-static
  # This code handler shared library must be called ${LOCAL_MPCONTEXT_NAME}-shared
  # It should also call generate_mpcontext_config_file with the correct parameters
  #  to create the target for generating the ${LOCAL_MPCONTEXT_NAME}.yml
  #  mpcontext configuration file.
  if ("${LOCAL_MPCONTEXT_NAME}" EQUAL "")
    message(WARNING "Directory ${name} did not provide a minpart context variable!")
  else()
    list(APPEND MPCONTEXT_TARGETS ${LOCAL_MPCONTEXT_NAME})
    set(MPCONTEXT_TARGETS ${MPCONTEXT_TARGETS} PARENT_SCOPE)
  endif()
endfunction()
# ==============================================================================
