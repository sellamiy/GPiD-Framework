# ==============================================================================
# CxxOpts - External minimal c++ cli options library - target
# ==============================================================================
project(libcxxopts LANGUAGES CXX)

configure_file(${CMAKE_SOURCE_DIR}/cmake/modules/CxxOpts.cmake.in
  ${CMAKE_BINARY_DIR}/cxxopts-download/CMakeLists.txt)
execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/cxxopts-download)
if(result)
  message(FATAL_ERROR "Download step for cxxopts failed: ${result}")
endif()
execute_process(COMMAND ${CMAKE_COMMAND} --build .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/cxxopts-download)
if(result)
  message(FATAL_ERROR "CMake step for cxxopts failed: ${result}")
endif()

add_subdirectory(${CMAKE_BINARY_DIR}/cxxopts-sources ${CMAKE_BINARY_DIR}/cxxopts-build EXCLUDE_FROM_ALL)
