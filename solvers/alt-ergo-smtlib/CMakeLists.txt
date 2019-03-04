# ==============================================================================
# Alt-Ergo Via partial SMTlib2 CLIs Solver Target
# ==============================================================================
find_package(AltErgo 2.2.0)
if (NOT AltErgo_FOUND)
  message(WARNING "Alt-Ergo not found")
  set(LOCAL_INTERFACE_NAME "" PARENT_SCOPE)
else()
  set(INTERFACE_HEADER_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/include/alt-ergo-smt2-interface.hpp.in")
  set(INTERFACE_HEADER "${LOCAL_SOLVER_INTERFACES_INCLUDE}/alt-ergo-smt2-interface.hpp")
  configure_file(${INTERFACE_HEADER_SOURCE} ${INTERFACE_HEADER})
  # ----------------------------------------------------------------------------
  add_library(saltergo-static INTERFACE)
  add_library(saltergo-shared INTERFACE)
  target_sources(saltergo-static INTERFACE ${INTERFACE_HEADER})
  target_sources(saltergo-shared INTERFACE ${INTERFACE_HEADER})
  target_include_directories(saltergo-static INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_include_directories(saltergo-shared INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_link_libraries(saltergo-static INTERFACE abdulot-static)
  target_link_libraries(saltergo-shared INTERFACE abdulot-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(saltergo
    alt-ergo-smt2-interface.hpp AltErgoPSmt2Interface abdulot::saihelpers::SMTl2SolverAbducibleGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME saltergo PARENT_SCOPE)
endif()
