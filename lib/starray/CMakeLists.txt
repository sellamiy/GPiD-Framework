# ==============================================================================
# Static arrays library - local library target
# ==============================================================================
project(libstarray LANGUAGES CXX)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/starray/starray.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/starray/starray.hpp)

file(GLOB LIBSTARRAY_SOURCES "src/*.cpp")

add_library(starray-static STATIC ${LIBSTARRAY_SOURCES})
add_library(starray-shared SHARED ${LIBSTARRAY_SOURCES})
target_link_libraries(starray-static snlog)
target_link_libraries(starray-shared snlog)
target_include_directories(starray-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
target_include_directories(starray-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
set_target_properties(starray-static PROPERTIES OUTPUT_NAME starray CLEAN_DIRECT_OUTPUT 1)
set_target_properties(starray-shared PROPERTIES OUTPUT_NAME starray CLEAN_DIRECT_OUTPUT 1)
