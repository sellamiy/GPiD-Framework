# ==============================================================================
# Script absorbtion utilities
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_python_module(colorama REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(CODEGEN_ABSORBTION_SCRIPT "${CMAKE_SOURCE_DIR}/utils/codegen/script-absorber.py")
# ==============================================================================
function(generate_absorbtion_file target_name target_file template_file) # ARGN: absorbtion_list
  add_custom_command(
    OUTPUT "${target_file}"
    DEPENDS "${CODEGEN_ABSORBTION_SCRIPT}" "${template_file}" ${ARGN}
    COMMAND "${PYTHON_EXECUTABLE}" "${CODEGEN_ABSORBTION_SCRIPT}"
    "--template=${template_file}" "--output=${target_file}"
    "--absorb" ${ARGN})
  add_custom_target(${target_name}
    DEPENDS "${target_file}" "${CODEGEN_ABSORBTION_SCRIPT}" "${template_file}" ${ARGN})
endfunction()
# ==============================================================================
