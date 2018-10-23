# ==============================================================================
# Static arrays library - local library target
# ==============================================================================
project(libstarray LANGUAGES CXX)
set(LIBSTARRAY_VERSION "0.4")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/starray/starray.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/starray/starray.hpp)

file(GLOB LIBSTARRAY_HEADERS "starray/*.hpp")
file(GLOB LIBSTARRAY_SOURCES "src/*.cpp")

add_library(starray-static STATIC ${LIBSTARRAY_SOURCES})
add_library(starray-shared SHARED ${LIBSTARRAY_SOURCES})
target_link_libraries(starray-static snlog)
target_link_libraries(starray-shared snlog)
target_include_directories(starray-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(starray-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(starray-static PROPERTIES
  OUTPUT_NAME starray
  VERSION ${LIBSTARRAY_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(starray-shared PROPERTIES
  OUTPUT_NAME starray
  VERSION ${LIBSTARRAY_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS starray-static starray-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBSTARRAY_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/starray/starray.hpp
  DESTINATION include/starray)
