# ==============================================================================
# WitchW Library - local library target
# ==============================================================================
project(libwitchw LANGUAGES CXX)
set(LIBWITCHW_VERSION "0.1")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/witchw/witchw.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/witchw/witchw.hpp)

file(GLOB LIBWITCHW_HEADERS "witchw/*.hpp")
file(GLOB LIBWITCHW_SOURCES "src/*.cpp")

add_library(witchw-static STATIC ${LIBWITCHW_SOURCES})
add_library(witchw-shared SHARED ${LIBWITCHW_SOURCES})
target_include_directories(witchw-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(witchw-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(witchw-static PROPERTIES
  OUTPUT_NAME witchw
  VERSION ${LIBWITCHW_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(witchw-shared PROPERTIES
  OUTPUT_NAME witchw
  VERSION ${LIBWITCHW_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS witchw-static witchw-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBWITCHW_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/witchw/witchw.hpp
  DESTINATION include/witchw)
