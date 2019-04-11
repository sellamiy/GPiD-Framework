# ==============================================================================
# Framework multi-executable wrap system
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_python_module(colorama REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(CODEGEN_WRAP_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/exewrap-generator.py")
file(GLOB CODEGEN_TEMPLATES "${CMAKE_SOURCE_DIR}/utils/templates/execwrap/*")
# ==============================================================================
function(generate_wrapper)
  set(options)
  set(oneValueArgs LANGUAGE TARGET)
  set(multiValueArgs EXECUTABLES)
  cmake_parse_arguments(WOPTS "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
  add_custom_command(
    OUTPUT "${WOPTS_TARGET}"
    DEPENDS "${CODEGEN_WRAP_SCRIPT}" ${CODEGEN_TEMPLATES} ${WOPTS_EXECUTABLES}
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_WRAP_SCRIPT}" "--executable"
    "--lang=${WOPTS_LANGUAGE}" "--output=${WOPTS_TARGET}" ${WOPTS_EXECUTABLES})
  add_custom_target(${WOPTS_LANGUAGE}-executable-wrappers ALL
    DEPENDS "${WOPTS_TARGET}" "${CODEGEN_WRAP_SCRIPT}" ${CODEGEN_TEMPLATES} ${WOPTS_EXECUTABLES})
  install(FILES "${WOPTS_TARGET}" DESTINATION bin)
endfunction()
# ==============================================================================
