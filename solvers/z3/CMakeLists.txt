# ==============================================================================
# z3 Solver Target
# ==============================================================================
find_package(Z3)
if (NOT Z3_FOUND)
  message(WARNING "Z3 not found")
  set(LOCAL_INTERFACE_NAME "" PARENT_SCOPE)
else()
  include_directories(${Z3_CXX_INCLUDE_DIRS})
  # ----------------------------------------------------------------------------
  file(GLOB INTERFACE_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
  file(GLOB INTERFACE_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
  # ----------------------------------------------------------------------------
  add_library(lz3-static STATIC ${INTERFACE_SOURCES})
  add_library(lz3-shared SHARED ${INTERFACE_SOURCES})
  target_include_directories(lz3-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  target_include_directories(lz3-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  set_target_properties(lz3-static PROPERTIES OUTPUT_NAME lz3-interface CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(lz3-shared PROPERTIES OUTPUT_NAME lz3-interface CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(lz3-static ${Z3_LIBRARIES} abdulot-static)
  target_link_libraries(lz3-shared ${Z3_LIBRARIES} abdulot-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(lz3
    z3-api-interface.hpp Z3InterfaceAPI Z3AbducibleLiteralsGenerator
    "--exception=\"z3::exception;msg\"")
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME lz3 PARENT_SCOPE)
endif()
