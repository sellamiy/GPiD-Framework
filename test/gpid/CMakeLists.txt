# ==============================================================================
# Tests configuration - gpid targets
# ==============================================================================
# == Result Testing Targets == gpid-minisat ==
if (TOOLEVAL_FOUND)
  file(GLOB TOOL_EVALUATION_SCRIPTS "tooleval/*Checker.tes")
  file(GLOB TOOL_EVALUATION_TOOLS "tooleval/*Tool.tes")
  foreach(checker ${TOOL_EVALUATION_SCRIPTS})
    compile_tooleval_script(${TESTS_RUNTIME_OUTPUT_DIRECTORY} ${checker} ${TOOL_EVALUATION_TOOLS})
    get_filename_component(checker_name "${checker}" NAME_WE)
    file(GLOB CHECKER_ARGS "tooleval-args/${checker_name}.arg.*")
    list(SORT CHECKER_ARGS)
    if (CHECKER_ARGS)
      add_test(NAME "ToolEval:${checker_name}"
        COMMAND "${TESTS_RUNTIME_OUTPUT_DIRECTORY}/${checker_name}" -s test -a ${CHECKER_ARGS}
        WORKING_DIRECTORY "${TESTS_RUNTIME_OUTPUT_DIRECTORY}")
    else()
      add_test(NAME "ToolEval:${checker_name}"
        COMMAND "${TESTS_RUNTIME_OUTPUT_DIRECTORY}/${checker_name}" -s test
        WORKING_DIRECTORY "${TESTS_RUNTIME_OUTPUT_DIRECTORY}")
    endif()
  endforeach()
else()
  message(WARNING "Tool Evaluation Script Compiler not found: Skipping related tests generation!")
endif()
# ==============================================================================
