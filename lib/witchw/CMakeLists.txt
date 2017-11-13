# ==============================================================================
# WitchW Library - local library target
# ==============================================================================
project(libwitchw LANGUAGES CXX)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/witchw/witchw.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/witchw/witchw.hpp)

file(GLOB LIBWITCHW_SOURCES "src/*.cpp")

add_library(witchw-static STATIC ${LIBWITCHW_SOURCES})
add_library(witchw-shared SHARED ${LIBWITCHW_SOURCES})
target_include_directories(witchw-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
target_include_directories(witchw-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
set_target_properties(witchw-static PROPERTIES OUTPUT_NAME witchw CLEAN_DIRECT_OUTPUT 1)
set_target_properties(witchw-shared PROPERTIES OUTPUT_NAME witchw CLEAN_DIRECT_OUTPUT 1)
