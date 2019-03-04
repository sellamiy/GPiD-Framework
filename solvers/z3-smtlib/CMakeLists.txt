# ==============================================================================
# z3 SMTlib2 via CLIs Solver Target
# ==============================================================================
find_package(Z3)
if (NOT Z3_FOUND)
  message(WARNING "Z3 not found")
  set(LOCAL_INTERFACE_NAME "" PARENT_SCOPE)
else()
  set(INTERFACE_HEADER_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/include/z3-smtl2-interface.hpp.in")
  set(INTERFACE_HEADER "${LOCAL_SOLVER_INTERFACES_INCLUDE}/z3-smtl2-interface.hpp")
  configure_file(${INTERFACE_HEADER_SOURCE} ${INTERFACE_HEADER})
  # ----------------------------------------------------------------------------
  add_library(cz3-static INTERFACE)
  add_library(cz3-shared INTERFACE)
  target_sources(cz3-static INTERFACE ${INTERFACE_HEADER})
  target_sources(cz3-shared INTERFACE ${INTERFACE_HEADER})
  target_include_directories(cz3-static INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_include_directories(cz3-shared INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_link_libraries(cz3-static INTERFACE abdulot-static)
  target_link_libraries(cz3-shared INTERFACE abdulot-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(cz3
    z3-smtl2-interface.hpp Z3InterfaceSMTl2CLI abdulot::saihelpers::SMTl2SolverAbducibleGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME cz3 PARENT_SCOPE)
endif()
