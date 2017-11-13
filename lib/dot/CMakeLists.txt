# ==============================================================================
# Dot - Dot graphs generation - local library target
# ==============================================================================
project(libdot LANGUAGES CXX)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/dot/dotgraph.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/dot/dotgraph.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/dot/dotcommand.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/dot/dotcommand.hpp)

file(GLOB LIBDOT_SOURCES "src/*.cpp")

add_library(dot-static STATIC ${LIBDOT_SOURCES})
add_library(dot-shared SHARED ${LIBDOT_SOURCES})
target_link_libraries(dot-static snlog)
target_link_libraries(dot-shared snlog)
target_include_directories(dot-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
target_include_directories(dot-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
set_target_properties(dot-static PROPERTIES OUTPUT_NAME dot CLEAN_DIRECT_OUTPUT 1)
set_target_properties(dot-shared PROPERTIES OUTPUT_NAME dot CLEAN_DIRECT_OUTPUT 1)
