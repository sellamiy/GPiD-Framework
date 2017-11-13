# ==============================================================================
# Executable utilities packed with the framework
# ==============================================================================
project(gpid-execs LANGUAGES CXX)
# ==============================================================================
# GTS - an implicate generator
# ==============================================================================
add_executable(gpid-gts "src/gpid-gts.cpp")
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-gts gpid-static witchw-static cxxopts)
else()
  target_link_libraries(gpid-gts gpid-shared witchw-shared cxxopts)
endif()
# ==============================================================================
# Parser - an abducible files parser
# ==============================================================================
add_executable(gpid-parser "src/gpid-parser.cpp")
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-parser gpid-core-static cxxopts)
else()
  target_link_libraries(gpid-parser gpid-core-shared cxxopts)
endif()
