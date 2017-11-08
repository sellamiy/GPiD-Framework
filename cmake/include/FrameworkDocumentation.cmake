# ==============================================================================
# Documentation targets configuration
# ==============================================================================
if(BUILD_DOC AND DOXYGEN_FOUND)

  set(DOXYGEN_INF ${CMAKE_CURRENT_SOURCE_DIR}/cmake/doxygen/doxygen.cfg.in)
  set(DOXYGEN_OUTF ${CMAKE_CURRENT_BINARY_DIR}/local/config/doxygen.cfg)

  if(CMAKE_BUILD_TYPE STREQUAL "Debug")
    set(DOCUMENT_HIDDEN_ELEMENTS "YES")
  else()
    set(DOCUMENT_HIDDEN_ELEMENTS "NO")
  endif()

  if(DOXYGEN_DOT_FOUND)
    set(DOXYGEN_HAVE_DOT_PARAM "YES")
  else()
    set(DOXYGEN_HAVE_DOT_PARAM "NO")
  endif()

  configure_file(${DOXYGEN_INF} ${DOXYGEN_OUTF} @ONLY)

  add_custom_target(doc
    COMMAND ${DOXYGEN_EXECUTABLE} ${DOXYGEN_OUTF}
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    COMMENT "Doxygen: Generating API documentation"
    VERBATIM)

else()
  message(WARNING "Doxygen was not found. No documentation generated.")
endif()
