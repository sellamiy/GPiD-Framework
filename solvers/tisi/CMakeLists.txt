# ==============================================================================
# Template inactive solver interface Target
# ------------------------------------------------------------------------------
# The goal of this template is to provide a documentation of what should be
#  implemented in an interface.
# ==============================================================================
file(GLOB INTERFACE_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
file(GLOB INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
# ------------------------------------------------------------------------------
add_library(tisi-static STATIC ${INTERFACE_SOURCES})
add_library(tisi-shared SHARED ${INTERFACE_SOURCES})
target_include_directories(tisi-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories(tisi-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
set_target_properties(tisi-static PROPERTIES OUTPUT_NAME tisi-interface CLEAN_DIRECT_OUTPUT 1)
set_target_properties(tisi-shared PROPERTIES OUTPUT_NAME tisi-interface CLEAN_DIRECT_OUTPUT 1)
target_link_libraries(tisi-static abdulot-static)
target_link_libraries(tisi-shared abdulot-shared)
# ----------------------------------------------------------------------------
include(FrameworkSolverRegistration)
generate_interface_config_file(tisi
  tisi.hpp TisiInterface TisiGenerator)
# ----------------------------------------------------------------------------
set(LOCAL_INTERFACE_NAME tisi PARENT_SCOPE)
