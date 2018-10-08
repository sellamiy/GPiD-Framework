# ==============================================================================
# Infoline - local library target
# ==============================================================================
project(libinfoline LANGUAGES CXX)
set(LIBINFOLINE_VERSION "0.1")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/infoline/infoline.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/infoline/infoline.hpp)

file(GLOB LIBINFOLINE_HEADERS "infoline/*.hpp")
file(GLOB LIBINFOLINE_SOURCES "src/*.cpp")

add_library(infoline-static STATIC ${LIBINFOLINE_SOURCES})
add_library(infoline-shared SHARED ${LIBINFOLINE_SOURCES})
# target_link_libraries(infoline-static ugly)
# target_link_libraries(infoline-shared ugly)
target_include_directories(infoline-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(infoline-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(infoline-static PROPERTIES
  OUTPUT_NAME infoline
  VERSION ${LIBINFOLINE_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(infoline-shared PROPERTIES
  OUTPUT_NAME infoline
  VERSION ${LIBINFOLINE_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS infoline-static infoline-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBINFOLINE_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/infoline/infoline.hpp
  DESTINATION include/infoline)
