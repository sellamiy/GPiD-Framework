# ==============================================================================
# Why3 - WhyML - C++ Wrapper ICH
# ==============================================================================
find_package(Why3 1.0.0)
# TODO: include_directories(**Why3 Stuff**)
# ------------------------------------------------------------------------------
if (NOT Why3_FOUND)
  message(WARNING "Why3 not found")
  set(LOCAL_ICH_NAME "" PARENT_SCOPE)
else ()
  file(GLOB ICH_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
  file(GLOB ICH_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
  # --------------------------------------------------------------------------
  add_library(w3wml-static STATIC ${ICH_SOURCES})
  add_library(w3wml-shared SHARED ${ICH_SOURCES})
  target_include_directories(w3wml-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  target_include_directories(w3wml-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  set_target_properties(w3wml-static PROPERTIES
    OUTPUT_NAME w3wml
    CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(w3wml-shared PROPERTIES
    OUTPUT_NAME w3wml
    CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(w3wml-static abdulot-static why3cpp-static)
  target_link_libraries(w3wml-shared abdulot-shared why3cpp-shared)
  # --------------------------------------------------------------------------
  include(FrameworkIlinvaRegistration)
  set(W3WML_HANDLED_INTERFACES ccvc4 cz3 saltergo)
  set(W3WML_NOT_AVAILABLE)
  foreach(interface ${W3WML_HANDLED_INTERFACES})
    list(FIND SOLVER_TARGETS ${interface} DV_DUMMY)
    if (${DV_DUMMY} LESS 0)
      list(APPEND W3WML_NOT_AVAILABLE ${interface})
    endif()
  endforeach()
  if (W3WML_NOT_AVAILABLE)
    list(REMOVE_ITEM W3WML_HANDLED_INTERFACES ${W3WML_NOT_AVAILABLE})
  endif()
  generate_ich_config_file(
    NAME w3wml
    HEADER why3-whyml-ich.hpp
    CONVERTERS why3-whyml-converters.hpp
    CLASSNAME W3WML_ICH
    INTERFACES ${W3WML_HANDLED_INTERFACES})
  # --------------------------------------------------------------------------
  set(LOCAL_ICH_NAME w3wml PARENT_SCOPE)
endif()
