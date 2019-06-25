# ==============================================================================
# Additional local libraries targets
# ==============================================================================
add_subdirectory(snlog)
add_subdirectory(stdutils)
add_subdirectory(ugly)
add_subdirectory(lcdot)
add_subdirectory(lisptp)
add_subdirectory(starray)
add_subdirectory(smtlib2tools)
add_subdirectory(cxxopts)
# ------------------------------------------------------------------------------
if (BUILD_ILINVA)
  add_subdirectory(antlr4)
  add_subdirectory(why3cpp)
endif()
# ==============================================================================
