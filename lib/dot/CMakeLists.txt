# ==============================================================================
# Dot - Dot graphs generation - local library target
# ==============================================================================
project(libdot LANGUAGES CXX)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/dot/dotgraph.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/dot/dotgraph.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/dot/dotcommand.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/dot/dotcommand.hpp)

file(GLOB LIBDOT_SOURCES "src/*.cpp")

add_library(dot STATIC ${LIBDOT_SOURCES})
target_link_libraries(dot snlog)
target_include_directories(dot PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
