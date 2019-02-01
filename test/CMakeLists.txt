# ==============================================================================
# Tests configuration - tests targets
# ==============================================================================
if(BUILD_TESTS)

  # ===== Configuring Test Framework =====

  # Download and unpack googletest at configure time
  configure_file(${CMAKE_SOURCE_DIR}/cmake/modules/GoogleTest.cmake.in
    ${CMAKE_BINARY_DIR}/googletest-download/CMakeLists.txt)
  execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
  if(result)
    message(FATAL_ERROR "CMake step for googletest failed: ${result}")
  endif()
  execute_process(COMMAND ${CMAKE_COMMAND} --build .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
  if(result)
    message(FATAL_ERROR "Build step for googletest failed: ${result}")
  endif()

  # Prevent overriding the parent project's compiler/linker
  # settings on Windows
  set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)

  # Add googletest directly to our build. This defines
  # the gtest and gtest_main targets.
  add_subdirectory(${CMAKE_BINARY_DIR}/googletest-src
    ${CMAKE_BINARY_DIR}/googletest-build EXCLUDE_FROM_ALL)

  # The gtest/gtest_main targets carry header search path
  # dependencies automatically when using CMake 2.8.11 or
  # later. Otherwise we have to add them here ourselves.
  if (CMAKE_VERSION VERSION_LESS 2.8.11)
    include_directories("${gtest_SOURCE_DIR}/include")
  endif()

  # ===== Generating Test Targets =====

  # == Unit Targets ==
  file(GLOB LIB_TEST_FILES "lib/*/*.cpp" "framework/*.cpp")
  foreach(filename ${LIB_TEST_FILES})
    get_filename_component(execname "${filename}" NAME_WE)
    add_executable(${execname} "${filename}")
    target_link_libraries(${execname} ugly)
    target_link_libraries(${execname} starray-static)
    target_link_libraries(${execname} abdulot-static)
    target_link_libraries(${execname} gtest gtest_main)
    set_target_properties(${execname} PROPERTIES RUNTIME_OUTPUT_DIRECTORY ${TESTS_RUNTIME_OUTPUT_DIRECTORY})
    add_test(NAME ${execname} COMMAND ${execname})
  endforeach()

  # == Dimacs Targets ==
  file(GLOB DIMACS_TEST_FILES "dimacs/basic/*.dimacs")
  foreach(filename ${DIMACS_TEST_FILES})
    get_filename_component(mfilename "${filename}" NAME)
    add_test(NAME "${mfilename}:Non-Failure" COMMAND gpid-minisatp --autogen-abducibles all -i "${filename}")
  endforeach()

  # == Abducible Parser Targets ==
  file(GLOB ABDUCE_TEST_FILES "abduce/*.abduce")
  foreach(filename ${ABDUCE_TEST_FILES})
    get_filename_component(mfilename "${filename}" NAME)
    add_test(NAME "${mfilename}:Parse" COMMAND abdulot-parser -i "${filename}")
  endforeach()

  # == Result Testing Targets == gts-minisat ==
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
          COMMAND "${TESTS_RUNTIME_OUTPUT_DIRECTORY}/${checker_name}" -s test -a ${CHECKER_ARGS})
      else()
        add_test(NAME "ToolEval:${checker_name}"
          COMMAND "${TESTS_RUNTIME_OUTPUT_DIRECTORY}/${checker_name}" -s test)
      endif()
    endforeach()
  else()
    message(WARNING "Tool Evaluation Script Compiler not found: Skipping related tests generation!")
  endif()

  # ===== Coverage =====

  if (COVERAGE_TOOLS)
    setup_target_for_coverage(NAME coverage EXECUTABLE ctest)
  endif()
endif()
