# ==============================================================================
# Tests configuration - parsers targets
# ==============================================================================
# == Abducible Parser Targets ==
file(GLOB ABDUCE_TEST_FILES "abduce/*.abduce")
foreach(filename ${ABDUCE_TEST_FILES})
  get_filename_component(mfilename "${filename}" NAME)
  add_test(NAME "${mfilename}:Parse" COMMAND abdulot-parser -i "${filename}")
endforeach()
# ==============================================================================
