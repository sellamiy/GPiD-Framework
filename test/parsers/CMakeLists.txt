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
# == Mlw Parser Targets ==
file(GLOB ABDUCE_TEST_FILES "mlw/*.mlw")
foreach(filename ${ABDUCE_TEST_FILES})
  get_filename_component(mfilename "${filename}" NAME)
  add_test(NAME "${mfilename}:Parse:Tokenize" COMMAND why3-tools -t "${filename}")
  add_test(NAME "${mfilename}:Parse:Annotate" COMMAND why3-tools -a "${filename}")
  add_test(NAME "${mfilename}:Parse:Extract" COMMAND why3-tools -e "${filename}")
endforeach()
# ==============================================================================
