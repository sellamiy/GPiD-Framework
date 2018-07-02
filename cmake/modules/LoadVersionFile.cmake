# ==============================================================================
# Version file loaders
# ==============================================================================
include(PythonUtils)
# ------------------------------------------------------------------------------
find_python_module(colorama REQUIRED)
find_python_module(yaml REQUIRED)
find_python_module(jinja2 REQUIRED)
# ==============================================================================
set(PY_VERSION_HANDLER "${CMAKE_SOURCE_DIR}/utils/codegen/version-handler.py")
set(PY_VERSION_TEMPLATE "${CMAKE_SOURCE_DIR}/framework/templates/src/version.cpp")
# ==============================================================================
macro(load_version_file version_file)
  execute_process(
    COMMAND "${PYTHON_EXECUTABLE}" "${PY_VERSION_HANDLER}"
    "--version-file=${version_file}" "--print-version"
    OUTPUT_VARIABLE VERSION
    RESULT_VARIABLE _LVRESULT
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE)
  if (_LVRESULT)
    message(FATAL_ERROR "Failed to obtain version file from handler")
    set(VERSION "Unrecovered")
  endif()
endmacro()
# ==============================================================================
macro(register_version_generator version_file target_file)
  add_custom_command(
    OUTPUT "${target_file}"
    DEPENDS "${PY_VERSION_HANDLER}" "${PY_VERSION_TEMPLATE}" "${version_file}"
    COMMAND "${PYTHON_EXECUTABLE}" "${PY_VERSION_HANDLER}"
    "--version-file=${version_file}" "--output=${target_file}" "--generate-source"
    "--template-directory=${CMAKE_SOURCE_DIR}/framework/templates/src")
endmacro()
# ==============================================================================
