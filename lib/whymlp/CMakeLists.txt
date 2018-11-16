# ==============================================================================
# Why3 WhyML Antlr parser library - local library target
# ==============================================================================
project(libwhymlp LANGUAGES CXX)
set(LIBWHYMLP_VERSION "0.1")
# ------------------------------------------------------------------------------
find_package(Antlr4 4.7.1 EXACT REQUIRED)
# ------------------------------------------------------------------------------
generate_antlr_parser(
  GRAMMAR ${CMAKE_CURRENT_SOURCE_DIR}/antlr4/WhyML.g4
  OUTDIR ${LOCAL_LIB_HEADERS_DIR}/whymlp/antlr4
  VISITOR LISTENER)
# ------------------------------------------------------------------------------
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/whymlp/whymlp.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/whymlp/whymlp.hpp)
# ------------------------------------------------------------------------------
file(GLOB LIBWHYMLP_HEADERS "whymlp/*.hpp")
list(APPEND LIBWHYMLP_HEADERS ${WhyML_HEADERS})
file(GLOB LIBWHYMLP_SOURCES "src/*.cpp")
list(APPEND LIBWHYMLP_SOURCES ${WhyML_SOURCES})
# ------------------------------------------------------------------------------
add_library(whymlp-static STATIC ${LIBWHYMLP_SOURCES})
add_library(whymlp-shared SHARED ${LIBWHYMLP_SOURCES})
target_link_libraries(whymlp-static antlr4_static snlog)
target_link_libraries(whymlp-shared antlr4_shared snlog)
target_include_directories(whymlp-static
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}"
  PRIVATE "${LOCAL_LIB_HEADERS_DIR}/whymlp/antlr4")
target_include_directories(whymlp-shared
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}"
  PRIVATE "${LOCAL_LIB_HEADERS_DIR}/whymlp/antlr4")
set_target_properties(whymlp-static PROPERTIES
  OUTPUT_NAME whymlp
  VERSION ${LIBWHYMLP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(whymlp-shared PROPERTIES
  OUTPUT_NAME whymlp
  VERSION ${LIBWHYMLP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
# ------------------------------------------------------------------------------
add_executable(whymlp-tools "bin/whymlp-tools.cpp")
target_link_libraries(whymlp-tools whymlp-static cxxopts)
# ------------------------------------------------------------------------------
install(TARGETS whymlp-static whymlp-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBWHYMLP_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/whymlp/whymlp.hpp
  DESTINATION include/whymlp)
install(TARGETS whymlp-tools RUNTIME DESTINATION bin)
# ------------------------------------------------------------------------------
