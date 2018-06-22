# ==============================================================================
# Pretty Compilable Trace - Compilable format trace export - local library target
# ==============================================================================
project(libpctrace LANGUAGES CXX)
set(LIBPCTRACE_VERSION "0.1")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/pctrace/pctrace.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/pctrace/pctrace.hpp)

file(GLOB LIBPCTRACE_HEADERS "pctrace/*.hpp")
file(GLOB LIBPCTRACE_SOURCES "src/*.cpp")

add_library(pctrace-static STATIC ${LIBPCTRACE_SOURCES})
add_library(pctrace-shared SHARED ${LIBPCTRACE_SOURCES})
# target_link_libraries(pctrace-static ugly)
# target_link_libraries(pctrace-shared ugly)
target_include_directories(pctrace-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(pctrace-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(pctrace-static PROPERTIES
  OUTPUT_NAME pctrace
  VERSION ${LIBPCTRACE_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(pctrace-shared PROPERTIES
  OUTPUT_NAME pctrace
  VERSION ${LIBPCTRACE_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS pctrace-static pctrace-shared
  ARCHIVE DESTINATION lib/static
  LIBRARY DESTINATION lib
  PUBLIC_HEADER DESTINATION include/pctrace)
install(FILES ${LIBPCTRACE_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/pctrace/pctrace.hpp
  DESTINATION include/pctrace)
