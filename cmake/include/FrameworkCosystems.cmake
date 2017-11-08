# ==============================================================================
# Project Cosystems configuration
# ==============================================================================
if (DOT_AUTOCOMPILATION)
  find_package(Dot REQUIRED)
endif()
# ==============================================================================
if (BUILD_DOC)
  find_package(Doxygen REQUIRED)
endif()
