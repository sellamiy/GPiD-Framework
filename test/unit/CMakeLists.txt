# ==============================================================================
# Tests configuration - unit tests
# ==============================================================================
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
# ==============================================================================
