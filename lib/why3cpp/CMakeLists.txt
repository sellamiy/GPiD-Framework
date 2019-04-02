# ==============================================================================
# Why3 C++ library - local library target
# ==============================================================================
project(libwhy3cpp LANGUAGES CXX)
set(LIBWHY3CPP_VERSION "0.4.0")
# ------------------------------------------------------------------------------
find_package(Antlr4 4.7.1 EXACT REQUIRED)
find_package(Why3 REQUIRED)
include(Why3Utils)
# ------------------------------------------------------------------------------
generate_antlr_parser(
  GRAMMAR ${CMAKE_CURRENT_SOURCE_DIR}/antlr4/WhyML.g4
  OUTDIR ${LOCAL_LIB_HEADERS_DIR}/why3cpp/antlr4
  VISITOR LISTENER)
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/why3cpp/why3cpp.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/why3cpp/why3cpp.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/why3cpp/why3config.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/why3cpp/why3config.hpp)
# ------------------------------------------------------------------------------
file(GLOB LIBWHY3CPP_HEADERS "why3cpp/*.hpp")
list(APPEND LIBWHY3CPP_HEADERS ${WhyML_HEADERS})
file(GLOB LIBWHY3CPP_SOURCES "src/*.cpp")
list(APPEND LIBWHY3CPP_SOURCES ${WhyML_SOURCES})
# -----------------------------------------
file(GLOB LIBWHY3CPP_HEADERS_TEMPLATES "templates/*.hpp")
file(GLOB LIBWHY3CPP_SOURCES_TEMPLATES "templates/*.cpp")
foreach(template ${LIBWHY3CPP_HEADERS_TEMPLATES})
  get_filename_component(edited_template "${template}" NAME)
  set(edited_template "${LOCAL_LIB_HEADERS_DIR}/why3cpp/${edited_template}")
  list(APPEND LIBWHY3CPP_HEADERS "${edited_template}")
  edit_why3cfg_template(TEMPLATE "${template}" OUTPUT "${edited_template}")
endforeach()
foreach(template ${LIBWHY3CPP_SOURCES_TEMPLATES})
  get_filename_component(edited_template "${template}" NAME)
  set(edited_template "${LOCAL_LIB_SOURCES_DIR}/why3cpp/${edited_template}")
  list(APPEND LIBWHY3CPP_SOURCES "${edited_template}")
  edit_why3cfg_template(TEMPLATE "${template}" OUTPUT "${edited_template}")
endforeach()
# ------------------------------------------------------------------------------
add_library(why3cpp-static STATIC ${LIBWHY3CPP_SOURCES})
add_library(why3cpp-shared SHARED ${LIBWHY3CPP_SOURCES})
foreach(template ${LIBWHY3CPP_HEADERS_TEMPLATES})
  get_filename_component(template_name "${template}" NAME_WE)
  add_dependencies(why3cpp-static ${template_name}-why3-edit)
  add_dependencies(why3cpp-shared ${template_name}-why3-edit)
endforeach()
target_link_libraries(why3cpp-static antlr4_static snlog smtlib2tools-static lisptp-static stdutils-static ugly)
target_link_libraries(why3cpp-shared antlr4_shared snlog smtlib2tools-shared lisptp-shared stdutils-shared ugly)
target_include_directories(why3cpp-static
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}"
  PRIVATE "${LOCAL_LIB_HEADERS_DIR}/why3cpp/antlr4" "${CMAKE_CURRENT_SOURCE_DIR}/private")
target_include_directories(why3cpp-shared
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}"
  PRIVATE "${LOCAL_LIB_HEADERS_DIR}/why3cpp/antlr4" "${CMAKE_CURRENT_SOURCE_DIR}/private")
set_target_properties(why3cpp-static PROPERTIES
  OUTPUT_NAME why3cpp
  VERSION ${LIBWHY3CPP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(why3cpp-shared PROPERTIES
  OUTPUT_NAME why3cpp
  VERSION ${LIBWHY3CPP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
# ------------------------------------------------------------------------------
add_executable(why3-tools "bin/why3-tools.cpp")
target_link_libraries(why3-tools why3cpp-static cxxopts)
# ------------------------------------------------------------------------------
install(TARGETS why3cpp-static why3cpp-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBWHY3CPP_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/why3cpp/why3cpp.hpp
  ${LOCAL_LIB_HEADERS_DIR}/why3cpp/why3config.hpp
  DESTINATION include/why3cpp)
install(TARGETS why3-tools RUNTIME DESTINATION bin)
# ------------------------------------------------------------------------------
