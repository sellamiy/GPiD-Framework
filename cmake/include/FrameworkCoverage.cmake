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
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/Library/Developer/CommandLineTools/SDKs/MacOSX10.14.sdk/usr/include/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "/Library/Developer/CommandLineTools/usr/include/c++/v1/*")

  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/cxxopts-sources/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/minisat-src/minisat/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/capsule/antlr/antlr4-sources/runtime/Cpp/runtime/src/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/capsule/antlr/antlr4-sources/runtime/Cpp/runtime/src/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/capsule/antlr/antlr4-sources/runtime/Cpp/runtime/src/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/local/lib/include/why3cpp/antlr4/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_BINARY_DIR}/googletest-src/*/*/*/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_SOURCE_DIR}/test/unit/lib/*/*")
  set(COVERAGE_EXCLUDES ${COVERAGE_EXCLUDES} "${CMAKE_SOURCE_DIR}/test/unit/framework/*/*")

  append_coverage_compiler_flags("-Wno-inline")

endif()
