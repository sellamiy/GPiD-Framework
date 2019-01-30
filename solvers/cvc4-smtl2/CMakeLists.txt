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
  add_library(ccvc4-static INTERFACE)
  add_library(ccvc4-shared INTERFACE)
  target_sources(ccvc4-static INTERFACE ${INTERFACE_HEADER})
  target_sources(ccvc4-shared INTERFACE ${INTERFACE_HEADER})
  target_include_directories(ccvc4-static INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_include_directories(ccvc4-shared INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_link_libraries(ccvc4-static INTERFACE gpid-core-static)
  target_link_libraries(ccvc4-shared INTERFACE gpid-core-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(ccvc4
    cvc4-smtl2-interface.hpp CVC4InterfaceSMTl2CLI SMTl2SolverAbducibleGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME ccvc4 PARENT_SCOPE)
endif()
