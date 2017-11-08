# ==============================================================================
# Static arrays library - local library target
# ==============================================================================
project(libstarray LANGUAGES CXX)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/starray/starray.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/starray/starray.hpp)

file(GLOB LIBSTARRAY_SOURCES "src/*.cpp")

add_library(starray STATIC ${LIBSTARRAY_SOURCES})
target_link_libraries(starray snlog)
target_include_directories(starray PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
