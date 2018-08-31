# ==============================================================================
# CVC4 SMTlib2 via CLIs Solver Target
# ==============================================================================
find_package(CVC4)
if (NOT CVC4_FOUND)
  message(WARNING "CVC4 not found")
else()
  set(INTERFACE_HEADER_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/include/cvc4-smtl2-interface.hpp.in")
  set(INTERFACE_HEADER "${LOCAL_SOLVER_INTERFACES_INCLUDE}/cvc4-smtl2-interface.hpp")
  configure_file(${INTERFACE_HEADER_SOURCE} ${INTERFACE_HEADER})
  # ----------------------------------------------------------------------------
  add_library(cvc4-smtl2-cli-static INTERFACE)
  add_library(cvc4-smtl2-cli-shared INTERFACE)
  target_sources(cvc4-smtl2-cli-static INTERFACE ${INTERFACE_HEADER})
  target_sources(cvc4-smtl2-cli-shared INTERFACE ${INTERFACE_HEADER})
  target_include_directories(cvc4-smtl2-cli-static INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_include_directories(cvc4-smtl2-cli-shared INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_link_libraries(cvc4-smtl2-cli-static INTERFACE gpid-core-static)
  target_link_libraries(cvc4-smtl2-cli-shared INTERFACE gpid-core-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(cvc4-smtl2-cli
    cvc4-smtl2-interface.hpp CVC4InterfaceSMTl2CLI SMTl2SolverAbducibleGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME cvc4-smtl2-cli PARENT_SCOPE)
endif()
