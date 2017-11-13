# ==============================================================================
# Framework coverage tools configuration
# ==============================================================================
if(COVERAGE_TOOLS)

  include(CodeCoverage)

  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/include/*" "/usr/include/c++/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/include/*/*" "/usr/include/c++/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/include/*/*/*" "/usr/include/c++/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/local/include/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/usr/local/include/cvc4/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/Applications/Xcode.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/include/c++/*/*")

  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/minisat-src/minisat/*/*")

  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_SOURCE_DIR}/test/lib/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_SOURCE_DIR}/test/framework/*/*")

  append_coverage_compiler_flags("-Wno-inline")

endif()
