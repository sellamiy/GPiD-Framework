# ==============================================================================
# Seperation logic formulas generators (for minimization)
# ==============================================================================
project(sl-formula-gen LANGUAGES NONE)
# ==============================================================================
set(SHEAP_RGEN_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/sheap/SLSHRandomGenerator.py")
set(SHEAP_RGEN_TARGET "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/sheap-rand")

add_custom_command(
  OUTPUT ${SHEAP_RGEN_TARGET}
  DEPENDS ${SHEAP_RGEN_SOURCE}
  COMMAND ${CMAKE_COMMAND} -E create_symlink ${SHEAP_RGEN_SOURCE} ${SHEAP_RGEN_TARGET})
add_custom_target(sheap-rand-gen ALL
  DEPENDS ${SHEAP_RGEN_TARGET} ${SHEAP_RGEN_SOURCE})
# ==============================================================================
