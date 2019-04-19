# ==============================================================================
# Tests configuration - ilinva targets
# ==============================================================================
find_package(Why3 1.0.0)
find_package(CVC4)
# ==============================================================================
# == Result Testing Targets == ilinva *** assuming why3 & cvc4 ==
if (CVC4_FOUND AND Why3_FOUND)
  file(GLOB MLW_TEST_TARGETS "${CMAKE_CURRENT_SOURCE_DIR}/mlw/*.mlw")
  file(MAKE_DIRECTORY "${CMAKE_BINARY_DIR}/ilinva-test/out")
  foreach(mlwtest ${MLW_TEST_TARGETS})
    get_filename_component(mlwtest_name "${mlwtest}" NAME_WE)
    set(mlwtest_abd "${CMAKE_CURRENT_SOURCE_DIR}/abd/${mlwtest_name}.abd")
    set(mlwtest_out "${CMAKE_BINARY_DIR}/ilinva-test/out/${mlwtest_name}.mlw")
    add_test(NAME "Ilinva:${mlwtest_name}:Generation"
      COMMAND ilinva-why3-wrapped -i "${mlwtest}" -a "${mlwtest_abd}" -o "${mlwtest_out}" -g ccvc4 --smt-time-limit=2 -s 1 -H "solver:CVC4" -H "vcreorder:false")
    add_test(NAME "Ilinva:${mlwtest_name}:Result"
      COMMAND ${WHY3_EXECUTABLE} prove -a split_vc -P CVC4 "${mlwtest_out}")
    set_tests_properties("Ilinva:${mlwtest_name}:Result"
      PROPERTIES DEPENDS "Ilinva:${mlwtest_name}:Generation")
  endforeach()
elseif (CVC4_FOUND)
  message(WARNING "Ilinva tests Skipped - Why3 required")
elseif (Why3_FOUND)
  message(WARNING "Ilinva tests Skipped - CVC4 (Smtlib) required")
else()
  message(WARNING "Ilinva tests Skipped - Why3 and CVC4 (Smtlib) required")
endif ()
# ==============================================================================
