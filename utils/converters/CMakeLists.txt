# ==============================================================================
# Benchmark Converters Tools
# ==============================================================================
project(benchmark-converters LANGUAGES NONE)
# ==============================================================================
set(SMT2ABDUCE_CONVERTER_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/smt2abduce/Smt2AbduceGenerator.py")
set(SMT2ABDUCE_CONVERTER_TARGET "${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/smt2abduce")

add_custom_command(
  OUTPUT ${SMT2ABDUCE_CONVERTER_TARGET}
  DEPENDS ${SMT2ABDUCE_CONVERTER_SOURCE}
  COMMAND ${CMAKE_COMMAND} -E create_symlink ${SMT2ABDUCE_CONVERTER_SOURCE} ${SMT2ABDUCE_CONVERTER_TARGET})
add_custom_target(smt2abduce-converter ALL
  DEPENDS ${SMT2ABDUCE_CONVERTER_TARGET} ${SMT2ABDUCE_CONVERTER_SOURCE})
# ==============================================================================
