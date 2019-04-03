# ==============================================================================
# Lisp Tree Parser library - local library target
# ==============================================================================
project(liblisptp LANGUAGES CXX)
set(LIBLISPTP_VERSION "0.2.3")

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/lisptp/lisptp.hpp.in
  ${LOCAL_LIB_HEADERS_DIR}/lisptp/lisptp.hpp)

file(GLOB LIBLISPTP_HEADERS "lisptp/*.hpp")
file(GLOB LIBLISPTP_SOURCES "src/*.cpp")

add_library(lisptp-static STATIC ${LIBLISPTP_SOURCES})
add_library(lisptp-shared SHARED ${LIBLISPTP_SOURCES})
target_link_libraries(lisptp-static snlog)
target_link_libraries(lisptp-shared snlog)
target_include_directories(lisptp-static PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
target_include_directories(lisptp-shared PUBLIC
  "${CMAKE_CURRENT_SOURCE_DIR}" "${LOCAL_LIB_HEADERS_DIR}")
set_target_properties(lisptp-static PROPERTIES
  OUTPUT_NAME lisptp
  VERSION ${LIBLISPTP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(lisptp-shared PROPERTIES
  OUTPUT_NAME lisptp
  VERSION ${LIBLISPTP_VERSION}
  CLEAN_DIRECT_OUTPUT 1)

install(TARGETS lisptp-static lisptp-shared
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib)
install(FILES ${LIBLISPTP_HEADERS}
  ${LOCAL_LIB_HEADERS_DIR}/lisptp/lisptp.hpp
  DESTINATION include/lisptp)
