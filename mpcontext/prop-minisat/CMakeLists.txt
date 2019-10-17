# ==============================================================================
# Minisat Propositional logic minpart context
# ==============================================================================
include(ImportMinisat)
# ==============================================================================
file(GLOB MPCONTEXT_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
file(GLOB MPCONTEXT_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
# --------------------------------------------------------------------------
add_library(prop-minisat-static STATIC ${MPCONTEXT_SOURCES})
add_library(prop-minisat-shared SHARED ${MPCONTEXT_SOURCES})
target_include_directories(prop-minisat-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${CMAKE_BINARY_DIR}/minisat-src")
target_include_directories(prop-minisat-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${CMAKE_BINARY_DIR}/minisat-src")
set_target_properties(prop-minisat-static PROPERTIES
  OUTPUT_NAME prop-minisat
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(prop-minisat-shared PROPERTIES
  OUTPUT_NAME prop-minisat
  CLEAN_DIRECT_OUTPUT 1)
target_link_libraries(prop-minisat-static minpart-static minisat-lib-static)
target_link_libraries(prop-minisat-shared minpart-shared minisat-lib-shared)
# --------------------------------------------------------------------------
include(FrameworkMinpartContextRegistration)
generate_mpcontext_config_file(
  NAME prop-minisat
  HEADER context-prop-minisat.hpp
  CLASSNAME minpart::prop::PropProblemContext
  OPTCLASSNAME minpart::prop::PropExecOpts)
# --------------------------------------------------------------------------
set(LOCAL_MPCONTEXT_NAME prop-minisat PARENT_SCOPE)
