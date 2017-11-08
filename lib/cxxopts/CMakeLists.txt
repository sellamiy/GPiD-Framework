# ==============================================================================
# CxxOpts - External minimal c++ cli options library - target
# ==============================================================================
project(libcxxopts LANGUAGES CXX)

add_library(cxxopts INTERFACE)

file(GLOB LIBCXXOPTS_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/cxxopts/*.hpp")
target_sources(cxxopts INTERFACE ${LIBCXXOPTS_SOURCES})
target_include_directories(cxxopts INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}")
