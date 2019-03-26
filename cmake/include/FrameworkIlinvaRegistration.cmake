# ==============================================================================
# Ilinva registration utilities
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_python_module(colorama REQUIRED)
find_python_module(yaml REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(CODEGEN_MULTI_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/multi-iph.py")
set(CODEGEN_CONFIG_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/config-iph.py")
# ==============================================================================
function(generate_iph_multi_file)
  set(options)
  set(oneValueArgs TARGET TEMPLATE)
  set(multiValueArgs IPHANDLERS)
  cmake_parse_arguments(IPHD "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
  set(IPH_CONFIG_FILES)
  set(IPH_CLI_OPTIONS)
  foreach(iph_id ${IPHD_IPHANDLERS})
    list(APPEND IPH_CONFIG_TARGETS ${iph_id}-config-file)
    list(APPEND IPH_CONFIG_FILES "${LOCAL_IPH_CONFIGS}/${iph_id}.yml")
    list(APPEND IPH_CLI_OPTIONS "--code-handler=${LOCAL_IPH_CONFIGS}/${iph_id}.yml")
  endforeach()
  add_custom_command(
    OUTPUT "${IPHD_TARGET}"
    DEPENDS "${CODEGEN_MULTI_SCRIPT}" "${IPHD_TEMPLATE}" ${IPH_CONFIG_FILES}
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_MULTI_SCRIPT}"
    "--source=${IPHD_TEMPLATE}" "--output=${IPHD_TARGET}" "--process"
    ${IPH_CLI_OPTIONS})
  get_filename_component(template_name "${IPHD_TEMPLATE}" NAME_WE)
  add_custom_target(${template_name}-multi
    DEPENDS "${IPHD_TARGET}" "${CODEGEN_MULTI_SCRIPT}" "${IPHD_TEMPLATE}" ${IPH_CONFIG_TARGETS})
endfunction()
# ------------------------------------------------------------------------------
function(generate_iph_config_file)
  set(options)
  set(oneValueArgs NAME HEADER CONVERTERS CLASSNAME)
  set(multiValueArgs INTERFACES EXCEPTIONS)
  cmake_parse_arguments(IPHD "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
  set(IPH_CONFIG_FILE "${LOCAL_IPH_CONFIGS}/${IPHD_NAME}.yml")
  set(IPH_ADDITIONAL_CLIS)
  foreach(iph_interface ${IPHD_INTERFACES})
    list(APPEND IPH_ADDITIONAL_CLIS "--interface=${LOCAL_SOLVER_INTERFACES_CONFIGS}/${iph_interface}.yml")
  endforeach()
  foreach(iph_exception ${IPHD_EXCEPTIONS})
    list(APPEND IPH_ADDITIONAL_CLIS "--exception=\"${iph_exception}\"")
  endforeach()
  add_custom_command(
    OUTPUT "${IPH_CONFIG_FILE}"
    DEPENDS "${CODEGEN_CONFIG_SCRIPT}"
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_CONFIG_SCRIPT}"
    "--code-handler=${IPHD_NAME}" "--output=${IPH_CONFIG_FILE}"
    "--mainheader=\"${IPHD_HEADER}\"" "--classname=${IPHD_CLASSNAME}"
    "--converters=\"${IPHD_CONVERTERS}\""
    ${IPH_ADDITIONAL_CLIS} "--generate")
  add_custom_target(${IPHD_NAME}-config-file
    DEPENDS "${IPH_CONFIG_FILE}" "${CODEGEN_CONFIG_SCRIPT}")
endfunction()
# ==============================================================================
function(load_iph_directory name)
  add_subdirectory(${name})
  # The previous call should set the following variables: LOCAL_IPH_NAME
  # This variable should contain the base name of the code handler.
  # This code handler static library must be called ${LOCAL_IPH_NAME}-static
  # This code handler shared library must be called ${LOCAL_IPH_NAME}-shared
  # It should also call generate_iph_config_file with the correct parameters
  #  to create the target for generating the ${LOCAL_IPH_NAME}.yml
  #  iph configuration file.
  if ("${LOCAL_IPH_NAME}" EQUAL "")
    message(WARNING "Directory ${name} did not provide an code-handler variable!")
  else()
    list(APPEND IPH_TARGETS ${LOCAL_IPH_NAME})
    set(IPH_TARGETS ${IPH_TARGETS} PARENT_SCOPE)
  endif()
endfunction()
# ==============================================================================
