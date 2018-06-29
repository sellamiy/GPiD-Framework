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
  add_library(cvc4-api-static STATIC ${INTERFACE_SOURCES})
  add_library(cvc4-api-shared SHARED ${INTERFACE_SOURCES})
  target_include_directories(cvc4-api-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  target_include_directories(cvc4-api-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  set_target_properties(cvc4-api-static PROPERTIES OUTPUT_NAME cvc4-api-interface CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(cvc4-api-shared PROPERTIES OUTPUT_NAME cvc4-api-interface CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(cvc4-api-static cvc4 cvc4parser gpid-core-static)
  target_link_libraries(cvc4-api-shared cvc4 cvc4parser gpid-core-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(cvc4-api
    cvc4-api-interface.hpp CVC4InterfaceAPI CVC4AbducibleLiteralsGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME cvc4-api PARENT_SCOPE)
endif()
