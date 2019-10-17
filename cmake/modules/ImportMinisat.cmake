# ==============================================================================
# Minisat Importer and patcher
# ==============================================================================
find_package(ZLIB REQUIRED)

if (EXISTS "${CMAKE_BINARY_DIR}/minisat-download/CMakeLists.txt")
  file(READ "${CMAKE_BINARY_DIR}/minisat-download/CMakeLists.txt" D2057_30P_CONTENT)
else()
  set(D2057_30P_CONTENT "")
endif()

configure_file(${CMAKE_SOURCE_DIR}/cmake/modules/Minisat.cmake.in
  ${CMAKE_BINARY_DIR}/minisat-download/CMakeLists.txt)

file(READ "${CMAKE_BINARY_DIR}/minisat-download/CMakeLists.txt" D2057_30A_CONTENT)

if (NOT "${D2057_30P_CONTENT}" STREQUAL "${D2057_30A_CONTENT}")
  # TODO: Try to find a solution that does not depend on a file read operation
  execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/minisat-download)
  if(result)
    message(FATAL_ERROR "CMake step for minisat failed: ${result}")
  endif()
  execute_process(COMMAND ${CMAKE_COMMAND} --build .
    RESULT_VARIABLE result
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/minisat-download )
  if(result)
    message(FATAL_ERROR "Download step for minisat failed: ${result}")
  endif()
endif()

get_property(MINISAT_IMPORTED GLOBAL PROPERTY MinisatImported)

if (NOT "${MINISAT_IMPORTED}" STREQUAL "YES")
  add_subdirectory(${CMAKE_BINARY_DIR}/minisat-src
    ${CMAKE_BINARY_DIR}/minisat-build
    EXCLUDE_FROM_ALL)
  SET_PROPERTY(GLOBAL PROPERTY MinisatImported "YES")
endif()
# ------------------------------------------------------------------------------
# include_directories("${CMAKE_BINARY_DIR}/minisat-src")
# ------------------------------------------------------------------------------
