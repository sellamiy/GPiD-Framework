# ==============================================================================
# Executable utilities packed with the framework
# ==============================================================================
project(gpid-execs LANGUAGES CXX)
# ==============================================================================
# GTS - an implicate generator
# ==============================================================================
add_executable(gpid-gts "src/gpid-gts.cpp")
target_link_libraries(gpid-gts gpid witchw cxxopts)
# ==============================================================================
# Parser - an abducible files parser
# ==============================================================================
add_executable(gpid-parser "src/gpid-parser.cpp")
target_link_libraries(gpid-parser gpid cxxopts)
