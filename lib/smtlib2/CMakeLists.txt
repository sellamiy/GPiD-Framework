# ==============================================================================
# Smtlib2 utilities library - local library target
# ==============================================================================
project(libsmtlib2utils LANGUAGES CXX)
set(LIBSMTLIB2UTILS_VERSION "0.1")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/smtlib2utils/smtlib2utils.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/smtlib2utils/smtlib2utils.hpp)

file(GLOB LIBSMTLIB2UTILS_HEADERS "smtlib2utils/*.hpp")
file(GLOB LIBSMTLIB2UTILS_SOURCES "src/*.cpp")

add_library(smtlib2utils-static STATIC ${LIBSMTLIB2UTILS_SOURCES})
add_library(smtlib2utils-shared SHARED ${LIBSMTLIB2UTILS_SOURCES})
target_link_libraries(smtlib2utils-static snlog)
target_link_libraries(smtlib2utils-shared snlog)
target_include_directories(smtlib2utils-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(smtlib2utils-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(smtlib2utils-static PROPERTIES
  OUTPUT_NAME smtlib2utils
  VERSION ${LIBSMTLIB2UTILS_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(smtlib2utils-shared PROPERTIES
  OUTPUT_NAME smtlib2utils
  VERSION ${LIBSMTLIB2UTILS_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS smtlib2utils-static smtlib2utils-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBSMTLIB2UTILS_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/smtlib2utils/smtlib2utils.hpp
  DESTINATION include/smtlib2utils)
