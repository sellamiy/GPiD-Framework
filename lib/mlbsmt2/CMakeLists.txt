# ==============================================================================
# Magic literal builder in Smtlib2 library - local library target
# ==============================================================================
project(libmlbsmt2 LANGUAGES CXX)
set(LIBMLBSMT2_VERSION "0.1")
# ------------------------------------------------------------------------------
include(PythonUtils)
find_package(PythonLibs 3 REQUIRED)
find_python_module(pysmt)
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/mlbsmt2/mlbsmt2.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/mlbsmt2/mlbsmt2.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/mlbsmt2/mlbconfig.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/mlbsmt2/mlbconfig.hpp)

file(GLOB LIBMLBSMT2_HEADERS "mlbsmt2/*.hpp")
file(GLOB LIBMLBSMT2_SOURCES "src/*.cpp")

add_library(mlbsmt2-static STATIC ${LIBMLBSMT2_SOURCES})
add_library(mlbsmt2-shared SHARED ${LIBMLBSMT2_SOURCES})
target_link_libraries(mlbsmt2-static snlog ${PYTHON_LIBRARIES})
target_link_libraries(mlbsmt2-shared snlog ${PYTHON_LIBRARIES})
target_include_directories(mlbsmt2-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
target_include_directories(mlbsmt2-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
set_target_properties(mlbsmt2-static PROPERTIES
  OUTPUT_NAME mlbsmt2
  VERSION ${LIBMLBSMT2_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(mlbsmt2-shared PROPERTIES
  OUTPUT_NAME mlbsmt2
  VERSION ${LIBMLBSMT2_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS mlbsmt2-static mlbsmt2-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBMLBSMT2_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/mlbsmt2/mlbsmt2.hpp
  DESTINATION include/mlbsmt2)
