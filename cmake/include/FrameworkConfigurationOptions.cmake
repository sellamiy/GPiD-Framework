# ==============================================================================
# Project options
# ==============================================================================
# Targets selection
# ==============================================================================
option(BUILD_TESTS "Build tests" ON)
option(COVERAGE_TOOLS "Configure and compile for code coverage reports" OFF)
option(GPID_INSTRUMENTATION "Activate gpid instrumentation toolset" OFF)
option(BUILD_DOC "Build documentation" ON)
option(STATIC_EXECUTABLES "Build executables using static librairies" ON)
# ==============================================================================
# Additional cosystems
# ==============================================================================
option(USE_COLORS "Configure color print outputs" ON)
option(DOT_AUTOCOMPILATION "Configure Dot graphs autocompilation" ON)
# ==============================================================================
# Code system
# ==============================================================================
option(MERGE_MINISAT_WRAPPERS "Merge Minisat wrappers into its original namespace" ON)
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
