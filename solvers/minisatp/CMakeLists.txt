# ==============================================================================
# Minisat Solver Target
# ==============================================================================
include(ImportMinisat)
# ==============================================================================
include(FrameworkSolverRegistration)
# ------------------------------------------------------------------------------
file(GLOB INTERFACE_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
file(GLOB INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
# ------------------------------------------------------------------------------
add_library(minisatp-static STATIC ${INTERFACE_SOURCES})
add_library(minisatp-shared SHARED ${INTERFACE_SOURCES})
target_include_directories(minisatp-static
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${CMAKE_BINARY_DIR}/minisat-src")
target_include_directories(minisatp-shared
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${CMAKE_BINARY_DIR}/minisat-src")
set_target_properties(minisatp-static PROPERTIES OUTPUT_NAME minisatp-interface CLEAN_DIRECT_OUTPUT 1)
set_target_properties(minisatp-shared PROPERTIES OUTPUT_NAME minisatp-interface CLEAN_DIRECT_OUTPUT 1)
target_link_libraries(minisatp-static minisat-lib-static abdulot-static)
target_link_libraries(minisatp-shared minisat-lib-shared abdulot-shared)
# ------------------------------------------------------------------------------
include(FrameworkSolverRegistration)
generate_interface_config_file(minisatp
  minisatp-interface.hpp MinisatInterface MinisatLiteralsGenerator)
# ------------------------------------------------------------------------------
set(LOCAL_INTERFACE_NAME minisatp PARENT_SCOPE)
