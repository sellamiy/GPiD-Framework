# ==============================================================================
# Antlr4 - LL(k) parser generator library - target
# ==============================================================================
project(libantlr4 LANGUAGES CXX)

set(ANTLR_BINARY_DIR "${CMAKE_BINARY_DIR}/capsule/antlr")

if (EXISTS "${ANTLR_BINARY_DIR}/antlr4-download/CMakeLists.txt")
  file(READ "${ANTLR_BINARY_DIR}/antlr4-download/CMakeLists.txt" D2050_30P_CONTENT)
else()
  set(D2050_30P_CONTENT "")
endif()

configure_file(${CMAKE_SOURCE_DIR}/cmake/modules/Antlr4.cmake.in
  ${ANTLR_BINARY_DIR}/antlr4-download/CMakeLists.txt)

file(READ "${ANTLR_BINARY_DIR}/antlr4-download/CMakeLists.txt" D2050_30A_CONTENT)

if (NOT "${D2050_30P_CONTENT}" STREQUAL "${D2050_30A_CONTENT}")
  # TODO: Try to find a solution that does not depend on a file read operation
  execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${ANTLR_BINARY_DIR}/antlr4-download)
  if(result)
    message(FATAL_ERROR "Download step for antlr4 failed: ${result}")
  endif()
  execute_process(COMMAND ${CMAKE_COMMAND} --build .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${ANTLR_BINARY_DIR}/antlr4-download)
  if(result)
    message(FATAL_ERROR "CMake step for antlr4 failed: ${result}")
  endif()
endif()

add_subdirectory(${ANTLR_BINARY_DIR}/antlr4-sources/runtime/Cpp
  ${ANTLR_BINARY_DIR}/antlr4-build EXCLUDE_FROM_ALL)
