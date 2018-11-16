# ==============================================================================
# Why3 Configuration file utilities
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_package(Why3 REQUIRED)
find_python_module(colorama REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(PY_WHY3_UTILITY_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/why3-tfe.py")
# ==============================================================================
function(edit_why3cfg_template)
  set(options)
  set(oneValueArgs TEMPLATE OUTPUT)
  set(multiValueArgs)
  cmake_parse_arguments(WEDITOR "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

  add_custom_command(
    OUTPUT "${WEDITOR_OUTPUT}"
    DEPENDS "${PY_WHY3_UTILITY_SCRIPT}" "${WEDITOR_TEMPLATE}"
    COMMAND "${PYTHON_EXECUTABLE}" "${PY_WHY3_UTILITY_SCRIPT}"
    "--patch" "--why3=\"${WHY3_EXECUTABLE}\""
    "--template=${WEDITOR_TEMPLATE}" "--output=${WEDITOR_OUTPUT}")
  get_filename_component(template_name "${WEDITOR_TEMPLATE}" NAME_WE)
  add_custom_target(${template_name}-why3-edit
    DEPENDS "${WEDITOR_OUTPUT}" "${PY_WHY3_UTILITY_SCRIPT}"  "${WEDITOR_TEMPLATE}")
endfunction()
# ==============================================================================
