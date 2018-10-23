# ==============================================================================
# Dot - Dot graphs generation - local library target
# ==============================================================================
project(liblcdot LANGUAGES CXX)
set(LIBLCDOT_VERSION "0.2")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/lcdot/dotgraph.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/lcdot/dotgraph.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/lcdot/dotcommand.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/lcdot/dotcommand.hpp)

file(GLOB LIBLCDOT_HEADERS "lcdot/*.hpp")
file(GLOB LIBLCDOT_SOURCES "src/*.cpp")

add_library(lcdot-static STATIC ${LIBLCDOT_SOURCES})
add_library(lcdot-shared SHARED ${LIBLCDOT_SOURCES})
target_link_libraries(lcdot-static snlog)
target_link_libraries(lcdot-shared snlog)
target_include_directories(lcdot-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(lcdot-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(lcdot-static PROPERTIES
  OUTPUT_NAME lcdot
  VERSION ${LIBLCDOT_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(lcdot-shared PROPERTIES
  OUTPUT_NAME lcdot
  VERSION ${LIBLCDOT_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS lcdot-static lcdot-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBLCDOT_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/lcdot/dotgraph.hpp
  ${LOCAL_LIB_HEADERS_DIR}/lcdot/dotcommand.hpp
  DESTINATION include/lcdot)
