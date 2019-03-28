# ==============================================================================
# Tests configuration - dimacs targets
# ==============================================================================
# == Dimacs Targets ==
file(GLOB DIMACS_TEST_FILES "basic/*.dimacs")
foreach(filename ${DIMACS_TEST_FILES})
  get_filename_component(mfilename "${filename}" NAME)
  add_test(NAME "${mfilename}:Non-Failure" COMMAND gpid-minisatp --autogen-abducibles all -i "${filename}")
endforeach()
# ==============================================================================
