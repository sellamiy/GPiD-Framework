# ==============================================================================
# WitchW Library - local library target
# ==============================================================================
project(libwitchw LANGUAGES CXX)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/witchw/witchw.hpp.in
  ${LOCAL_LIBRARIES_DIRECTORY}/witchw/witchw.hpp)

file(GLOB LIBWITCHW_SOURCES "src/*.cpp")

add_library(witchw STATIC ${LIBWITCHW_SOURCES})
target_include_directories(witchw PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIBRARIES_DIRECTORY}")
