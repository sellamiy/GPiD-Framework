# ==============================================================================
# z3 SMTlib2 via CLIs Solver Target
# ==============================================================================
find_package(Z3)
if (NOT Z3_FOUND)
  message(WARNING "Z3 not found")
else()
  set(INTERFACE_HEADER_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/include/z3-smtl2-interface.hpp.in")
  set(INTERFACE_HEADER "${LOCAL_SOLVER_INTERFACES_INCLUDE}/z3-smtl2-interface.hpp")
  configure_file(${INTERFACE_HEADER_SOURCE} ${INTERFACE_HEADER})
  # ----------------------------------------------------------------------------
  add_library(z3-smtl2-cli-static INTERFACE)
  add_library(z3-smtl2-cli-shared INTERFACE)
  target_sources(z3-smtl2-cli-static INTERFACE ${INTERFACE_HEADER})
  target_sources(z3-smtl2-cli-shared INTERFACE ${INTERFACE_HEADER})
  target_include_directories(z3-smtl2-cli-static INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_include_directories(z3-smtl2-cli-shared INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_link_libraries(z3-smtl2-cli-static INTERFACE gpid-core-static)
  target_link_libraries(z3-smtl2-cli-shared INTERFACE gpid-core-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(z3-smtl2-cli
    z3-smtl2-interface.hpp Z3InterfaceSMTl2CLI SMTl2SolverAbducibleGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME z3-smtl2-cli PARENT_SCOPE)
endif()
