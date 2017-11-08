# ==============================================================================
# Simple minimal logging library - local library target
# ==============================================================================
project(libsnlog LANGUAGES CXX)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/snlog/snlog.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/snlog/snlog.hpp)

add_library(snlog INTERFACE)

file(GLOB LIBSNLOG_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/snlog/*.hpp")
target_sources(snlog INTERFACE ${LIBSNLOG_SOURCES})
target_include_directories(snlog INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}" ${LOCAL_LIBRARIES_DIRECTORY})
