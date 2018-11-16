# - Try to find Antlr4
# ANTLR4_FOUND
# ANTLR4_EXECUTABLE

find_package(Java COMPONENTS Runtime REQUIRED)

file(DOWNLOAD
  https://www.antlr.org/download/antlr-4.7.1-complete.jar
  "${CMAKE_BINARY_DIR}/antlr/4.7.1/antlr-4.7.1-complete.jar"
  STATUS ANTLR4_DOWNLOAD_STATUS)

if (ANTLR4_DOWNLOAD_STATUS EQUAL 0)
  set(ANTLR4_EXECUTABLE java -jar "${CMAKE_BINARY_DIR}/antlr/4.7.1/antlr-4.7.1-complete.jar")
else()
  message(WARNING "Antlr4 Download failed, trying to find local version")
  find_program(ANTLR4_EXECUTABLE NAMES antlr4 antlr)
endif()
mark_as_advanced(ANTLR4_EXECUTABLE)

if (ANTLR4_EXECUTABLE)
  execute_process (COMMAND ${ANTLR4_EXECUTABLE}
    OUTPUT_VARIABLE antlr_version
    ERROR_QUIET
    OUTPUT_STRIP_TRAILING_WHITESPACE)
  string(REGEX REPLACE ";" "\\\\;" antlr_version "${antlr_version}")
  string(REGEX REPLACE "\n" ";" antlr_version "${antlr_version}")
  list(GET antlr_version 0 ANTLR4_VERSION_STRING)
  if (ANTLR4_VERSION_STRING MATCHES "^ANTLR Parser Generator  Version ([0-9]+)\\.([0-9]+)\\.([0-9]+)")
    string (REPLACE "ANTLR Parser Generator  Version " "" ANTLR4_VERSION_STRING ${ANTLR4_VERSION_STRING})
  endif()
endif()
mark_as_advanced(ANTLR4_VERSION_STRING)

function(generate_antlr_parser)
  set(options VISITOR LISTENER)
  set(oneValueArgs OUTDIR GRAMMAR)
  set(multiValueArgs)
  cmake_parse_arguments(FARGS "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})

  get_filename_component(FARGS_LIBDIR "${FARGS_GRAMMAR}" DIRECTORY)
  get_filename_component(FARGS_GRAMMAR "${FARGS_GRAMMAR}" NAME)
  get_filename_component(FARGS_NAME "${FARGS_GRAMMAR}" NAME_WE)

  set(FARGS_HEADERS
    "${FARGS_OUTDIR}/${FARGS_NAME}Lexer.h"
    "${FARGS_OUTDIR}/${FARGS_NAME}Parser.h")
  set(FARGS_SOURCES
    "${FARGS_OUTDIR}/${FARGS_NAME}Lexer.cpp"
    "${FARGS_OUTDIR}/${FARGS_NAME}Parser.cpp")
  set(FARGS_BYPRODUCTS
    "${FARGS_OUTDIR}/${FARGS_NAME}.interp"
    "${FARGS_OUTDIR}/${FARGS_NAME}.tokens"
    "${FARGS_OUTDIR}/${FARGS_NAME}Lexer.interp"
    "${FARGS_OUTDIR}/${FARGS_NAME}Lexer.tokens")
  set(GENERATION_OPTS)

  if (FARGS_VISITOR)
    list(APPEND GENERATION_OPTS "-visitor")
    list(APPEND FARGS_HEADERS "${FARGS_OUTDIR}/${FARGS_NAME}Visitor.h")
    list(APPEND FARGS_HEADERS "${FARGS_OUTDIR}/${FARGS_NAME}BaseVisitor.h")
    list(APPEND FARGS_BYPRODUCTS "${FARGS_OUTDIR}/${FARGS_NAME}Visitor.cpp")
    list(APPEND FARGS_BYPRODUCTS "${FARGS_OUTDIR}/${FARGS_NAME}BaseVisitor.cpp")
  else()
    list(APPEND GENERATION_OPTS "-no-visitor")
  endif()

  if (FARGS_LISTENER)
    list(APPEND GENERATION_OPTS "-listener")
    list(APPEND FARGS_HEADERS "${FARGS_OUTDIR}/${FARGS_NAME}Listener.h")
    list(APPEND FARGS_HEADERS "${FARGS_OUTDIR}/${FARGS_NAME}BaseListener.h")
    list(APPEND FARGS_BYPRODUCTS "${FARGS_OUTDIR}/${FARGS_NAME}Listener.cpp")
    list(APPEND FARGS_BYPRODUCTS "${FARGS_OUTDIR}/${FARGS_NAME}BaseListener.cpp")
  else()
    list(APPEND GENERATION_OPTS "-no-listener")
  endif()

  add_custom_command(
    OUTPUT ${FARGS_HEADERS} ${FARGS_SOURCES} ${FARGS_BYPRODUCTS}
    DEPENDS "${FARGS_LIBDIR}/${FARGS_GRAMMAR}"
    COMMAND ${ANTLR4_EXECUTABLE} -Dlanguage=Cpp ${GENERATION_OPTS}
    -o "${FARGS_OUTDIR}" -lib "${FARGS_LIBDIR}" "${FARGS_LIBDIR}/${FARGS_GRAMMAR}"
    COMMENT "Generating Cxx parser for grammar ${FARGS_NAME}")
  add_custom_target(${FARGS_NAME}-sources
    DEPENDS ${FARGS_HEADERS} ${FARGS_SOURCES} ${FARGS_BYPRODUCTS}
    "${FARGS_LIBDIR}/${FARGS_GRAMMAR}")

  set(${FARGS_NAME}_HEADERS ${FARGS_HEADERS} PARENT_SCOPE)
  set(${FARGS_NAME}_SOURCES ${FARGS_SOURCES} PARENT_SCOPE)
endfunction()

find_package_handle_standard_args(Antlr4
  REQUIRED_VARS ANTLR4_EXECUTABLE
  VERSION_VAR ANTLR4_VERSION_STRING)
