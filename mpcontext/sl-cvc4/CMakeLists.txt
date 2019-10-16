# ==============================================================================
# CVC4 Separation logic minpart context
# ==============================================================================
find_package(CVC4)
# ------------------------------------------------------------------------------
if (NOT CVC4_FOUND)
  message(ERROR "CVC4 not found --- cannot build related minpart-sl context")
  set(LOCAL_MPCONTEXT_NAME "" PARENT_SCOPE)
else ()
  file(GLOB MPCONTEXT_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
  file(GLOB MPCONTEXT_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
  # --------------------------------------------------------------------------
  configure_file("${CMAKE_CURRENT_SOURCE_DIR}/include/cvc4-config.hpp.in" "${LOCAL_MPCONTEXT_INCLUDE}/sl-cvc4/cvc4-config.hpp")
  # --------------------------------------------------------------------------
  add_library(sl-cvc4-static STATIC ${MPCONTEXT_SOURCES})
  add_library(sl-cvc4-shared SHARED ${MPCONTEXT_SOURCES})
  target_include_directories(sl-cvc4-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${LOCAL_MPCONTEXT_INCLUDE}/sl-cvc4")
  target_include_directories(sl-cvc4-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include" "${LOCAL_MPCONTEXT_INCLUDE}/sl-cvc4")
  set_target_properties(sl-cvc4-static PROPERTIES
    OUTPUT_NAME sl-cvc4
    CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(sl-cvc4-shared PROPERTIES
    OUTPUT_NAME sl-cvc4
    CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(sl-cvc4-static minpart-static lisptp-static ${CVC4_LIBRARIES})
  target_link_libraries(sl-cvc4-shared minpart-shared lisptp-shared ${CVC4_LIBRARIES})
  # --------------------------------------------------------------------------
  include(FrameworkMinpartContextRegistration)
  generate_mpcontext_config_file(
    NAME sl-cvc4
    HEADER context-sl-cvc4.hpp
    CLASSNAME minpart::slcvc::SLProblemContext
    OPTCLASSNAME minpart::slcvc::SLExecOpts)
  # --------------------------------------------------------------------------
  set(LOCAL_MPCONTEXT_NAME sl-cvc4 PARENT_SCOPE)
endif()
