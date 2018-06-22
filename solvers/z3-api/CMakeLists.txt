# ==============================================================================
# z3 Solver Target
# ==============================================================================
find_package(Z3)
if (NOT Z3_FOUND)
  message(WARNING "Z3 not found")
else()
  include_directories(${Z3_CXX_INCLUDE_DIRS})
  # ----------------------------------------------------------------------------
  file(GLOB INTERFACE_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
  file(GLOB INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
  # ----------------------------------------------------------------------------
  add_library(z3-api-static STATIC ${INTERFACE_SOURCES})
  add_library(z3-api-shared SHARED ${INTERFACE_SOURCES})
  target_include_directories(z3-api-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  target_include_directories(z3-api-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  set_target_properties(z3-api-static PROPERTIES OUTPUT_NAME z3-api-interface CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(z3-api-shared PROPERTIES OUTPUT_NAME z3-api-interface CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(z3-api-static ${Z3_LIBRARIES} gpid-core-static)
  target_link_libraries(z3-api-shared ${Z3_LIBRARIES} gpid-core-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(z3-api z3-api-interface.hpp Z3InterfaceAPI Z3AbducibleLiteralsGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME z3-api PARENT_SCOPE)
endif()
