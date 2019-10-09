# ==============================================================================
# Project options
# ==============================================================================
# Targets selection
# ==============================================================================
option(BUILD_TESTS "Build tests" ON)
option(BUILD_TOOLEVAL "Build tooleval scripts" ON)
option(BUILD_UTILITIES "Build additional tools, notably for benchmarking" ON)
option(COVERAGE_TOOLS "Configure and compile for code coverage reports" OFF)
option(INSTRUMENTATION "Activate gpid instrumentation toolset" OFF)
option(BUILD_DOC "Build documentation" ON)
option(STATIC_EXECUTABLES "Build executables using static librairies" ON)
option(BUILD_GLOBAL_WRAPPER "Build a global executable wrapping them all" ON)
option(BUILD_GPID "Build the prime implicate generator GPiD" ON)
option(BUILD_ILINVA "Build the loop invariant generator Ilinva" ON)
option(BUILD_MINPART_SL "Build the SL minpart model minimizer" ON)
# ==============================================================================
# Additional cosystems
# ==============================================================================
option(USE_COLORS "Configure color print outputs" ON)
option(DOT_AUTOCOMPILATION "Configure Dot graphs autocompilation" ON)
# ==============================================================================
# Computed options
# ==============================================================================
if(USE_COLORS AND NOT WIN32)
  set(USE_ANSI_COLORS "ON")
endif()
if(COVERAGE_TOOLS AND NOT BUILD_TESTS)
  message(WARNING "Forcing test compilation for building coverage tools!")
  set(BUILD_TESTS ON CACHE BOOL "Forcefully build tests systems" FORCE)
endif()
