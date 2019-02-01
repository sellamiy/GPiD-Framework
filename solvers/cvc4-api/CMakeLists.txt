# ==============================================================================
# CVC4 Solver Target
# ==============================================================================
find_package(CVC4)
if (NOT CVC4_FOUND)
  message(WARNING "CVC4 not found")
else()
  include_directories(${CVC4_INCLUDE_DIR})
  # ----------------------------------------------------------------------------
  file(GLOB INTERFACE_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
  file(GLOB INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
  # ----------------------------------------------------------------------------
  add_library(lcvc4-static STATIC ${INTERFACE_SOURCES})
  add_library(lcvc4-shared SHARED ${INTERFACE_SOURCES})
  target_include_directories(lcvc4-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  target_include_directories(lcvc4-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  set_target_properties(lcvc4-static PROPERTIES OUTPUT_NAME lcvc4-interface CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(lcvc4-shared PROPERTIES OUTPUT_NAME lcvc4-interface CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(lcvc4-static cvc4 cvc4parser abdulot-static)
  target_link_libraries(lcvc4-shared cvc4 cvc4parser abdulot-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(lcvc4
    cvc4-api-interface.hpp CVC4InterfaceAPI CVC4AbducibleLiteralsGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME lcvc4 PARENT_SCOPE)
endif()
