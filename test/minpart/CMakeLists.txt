# ==============================================================================
# Tests configuration - minpart results tests and generators
# ==============================================================================
# == Token Stack Formulas Target ==
set(LITS_RGEN_EXEC_FILE "lits/generator.cpp")
add_executable(minpart-lits-gen "${LITS_RGEN_EXEC_FILE}")
target_link_libraries(minpart-lits-gen minpart-static)
set_target_properties(minpart-lits-gen PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${TESTS_RUNTIME_OUTPUT_DIRECTORY})
# ==============================================================================
