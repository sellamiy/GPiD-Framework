# ==============================================================================
# Smtlib2 literal tools library - local library target
# ==============================================================================
project(libsmtlit LANGUAGES CXX)
set(LIBSMTLIT_VERSION "0.1")
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/smtlit/smtlit.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/smtlit/smtlit.hpp)

file(GLOB LIBSMTLIT_HEADERS "smtlit/*.hpp")
file(GLOB LIBSMTLIT_SOURCES "src/*.cpp")
# ------------------------------------------------------------------------------
add_library(smtlit-static STATIC ${LIBSMTLIT_SOURCES})
add_library(smtlit-shared SHARED ${LIBSMTLIT_SOURCES})
target_link_libraries(smtlit-static snlog smtlib2utils-static whymlp-static ugly)
target_link_libraries(smtlit-shared snlog smtlib2utils-shared whymlp-shared ugly)
target_include_directories(smtlit-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
target_include_directories(smtlit-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
set_target_properties(smtlit-static PROPERTIES
  OUTPUT_NAME smtlit
  VERSION ${LIBSMTLIT_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(smtlit-shared PROPERTIES
  OUTPUT_NAME smtlit
  VERSION ${LIBSMTLIT_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS smtlit-static smtlit-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBSMTLIT_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/smtlit/smtlit.hpp
  DESTINATION include/smtlit)
