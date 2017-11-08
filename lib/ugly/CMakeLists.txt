# ==============================================================================
# Libugly - local library target
# ==============================================================================
project(libugly LANGUAGES CXX)

add_library(ugly INTERFACE)

file(GLOB LIBUGLY_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/ugly/*.hpp")
target_sources(ugly INTERFACE ${LIBUGLY_SOURCES})
target_include_directories(ugly INTERFACE "${CMAKE_CURRENT_SOURCE_DIR}")
