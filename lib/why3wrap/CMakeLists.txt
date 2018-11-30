# ==============================================================================
# Why3 C++ Wrapper library - local library target
# ==============================================================================
project(libwhy3wrap LANGUAGES CXX)
set(LIBWHY3WRAP_VERSION "0.1")
# ------------------------------------------------------------------------------
find_package(Why3 REQUIRED)
include(Why3Utils)
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/why3wrap/why3wrap.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/why3wrap/why3wrap.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/why3wrap/why3config.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/why3wrap/why3config.hpp)
# ------------------------------------------------------------------------------
file(GLOB LIBWHY3WRAP_HEADERS "why3wrap/*.hpp")
file(GLOB LIBWHY3WRAP_SOURCES "src/*.cpp")
file(GLOB LIBWHY3WRAP_HEADERS_TEMPLATES "templates/*.hpp")
file(GLOB LIBWHY3WRAP_SOURCES_TEMPLATES "templates/*.cpp")
foreach(template ${LIBWHY3WRAP_HEADERS_TEMPLATES})
  get_filename_component(edited_template "${template}" NAME)
  set(edited_template "${LOCAL_LIB_HEADERS_DIR}/why3wrap/${edited_template}")
  list(APPEND LIBWHY3WRAP_HEADERS "${edited_template}")
  edit_why3cfg_template(TEMPLATE "${template}" OUTPUT "${edited_template}")
endforeach()
foreach(template ${LIBWHY3WRAP_SOURCES_TEMPLATES})
  get_filename_component(edited_template "${template}" NAME)
  set(edited_template "${LOCAL_LIB_SOURCES_DIR}/why3wrap/${edited_template}")
  list(APPEND LIBWHY3WRAP_SOURCES "${edited_template}")
  edit_why3cfg_template(TEMPLATE "${template}" OUTPUT "${edited_template}")
endforeach()
# ------------------------------------------------------------------------------
add_library(why3wrap-static STATIC ${LIBWHY3WRAP_SOURCES})
add_library(why3wrap-shared SHARED ${LIBWHY3WRAP_SOURCES})
foreach(template ${LIBWHY3WRAP_HEADERS_TEMPLATES})
  get_filename_component(template_name "${template}" NAME_WE)
  add_dependencies(why3wrap-static ${template_name}-why3-edit)
  add_dependencies(why3wrap-shared ${template_name}-why3-edit)
endforeach()
target_link_libraries(why3wrap-static snlog smtlib2tools-static lisptp-static)
target_link_libraries(why3wrap-shared snlog smtlib2tools-shared lisptp-shared)
target_include_directories(why3wrap-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
target_include_directories(why3wrap-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}" ${PYTHON_INCLUDE_DIRS})
set_target_properties(why3wrap-static PROPERTIES
  OUTPUT_NAME why3wrap
  VERSION ${LIBWHY3WRAP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(why3wrap-shared PROPERTIES
  OUTPUT_NAME why3wrap
  VERSION ${LIBWHY3WRAP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS why3wrap-static why3wrap-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBWHY3WRAP_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/why3wrap/why3wrap.hpp
  DESTINATION include/why3wrap)
