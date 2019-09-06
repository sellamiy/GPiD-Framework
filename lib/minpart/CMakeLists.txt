# ==============================================================================
# Minimal partition generalization C++ library - local library target
# ==============================================================================
project(libminpart LANGUAGES CXX)
set(LIBMINPART_VERSION "0.11.0")
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/minpart/minpart.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/minpart/minpart.hpp)

file(GLOB LIBMINPART_HEADERS "minpart/*.hpp")
file(GLOB LIBMINPART_EXAMPLES_HEADERS "minpart-contexts/*.hpp")
file(GLOB LIBMINPART_SOURCES "src/*.cpp")
# ------------------------------------------------------------------------------
add_library(minpart-static STATIC ${LIBMINPART_SOURCES})
add_library(minpart-shared SHARED ${LIBMINPART_SOURCES})
target_link_libraries(minpart-static stdutils-static)
target_link_libraries(minpart-shared stdutils-shared)
target_include_directories(minpart-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(minpart-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(minpart-static PROPERTIES
  OUTPUT_NAME minpart
  VERSION ${LIBMINPART_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(minpart-shared PROPERTIES
  OUTPUT_NAME minpart
  VERSION ${LIBMINPART_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
# ------------------------------------------------------------------------------
register_executable(minpart-lmmfp "bin/minpart-lmmfp.cpp")
target_link_libraries(minpart-lmmfp minpart-static cxxopts)
# ------------------------------------------------------------------------------
install(TARGETS minpart-static minpart-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBMINPART_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/minpart/minpart.hpp
  DESTINATION include/minpart)
install(TARGETS minpart-lmmfp RUNTIME DESTINATION bin)
