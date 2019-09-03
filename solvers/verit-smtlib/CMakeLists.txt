# ==============================================================================
# VeriT SMTlib2 CLIs Solver Target
# ==============================================================================
find_package(VeriT)
if (NOT VERIT_FOUND)
  message(WARNING "VeriT not found")
  set(LOCAL_INTERFACE_NAME "" PARENT_SCOPE)
else()
  set(INTERFACE_HEADER_SOURCE "${CMAKE_CURRENT_SOURCE_DIR}/include/verit-interface.hpp.in")
  set(INTERFACE_HEADER "${LOCAL_SOLVER_INTERFACES_INCLUDE}/verit-interface.hpp")
  configure_file(${INTERFACE_HEADER_SOURCE} ${INTERFACE_HEADER})
  # ----------------------------------------------------------------------------
  add_library(verit-static INTERFACE)
  add_library(verit-shared INTERFACE)
  target_sources(verit-static INTERFACE ${INTERFACE_HEADER})
  target_sources(verit-shared INTERFACE ${INTERFACE_HEADER})
  target_include_directories(verit-static INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_include_directories(verit-shared INTERFACE "${LOCAL_SOLVER_INTERFACES_INCLUDE}")
  target_link_libraries(verit-static INTERFACE abdulot-static)
  target_link_libraries(verit-shared INTERFACE abdulot-shared)
  # ----------------------------------------------------------------------------
  include(FrameworkSolverRegistration)
  generate_interface_config_file(verit
    verit-interface.hpp VeriTCLIInterface abdulot::saihelpers::SMTl2SolverAbducibleGenerator)
  # ----------------------------------------------------------------------------
  set(LOCAL_INTERFACE_NAME verit PARENT_SCOPE)
endif()
