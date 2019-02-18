# ==============================================================================
# Why3 - WhyML - C++ Wrapper ICH
# ==============================================================================
# TODO: Find Why3 and related; Do the following only if found; else message
# TODO: include_directories(**Why3 Stuff**)
# ----------------------------------------------------------------------------
file(GLOB ICH_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
file(GLOB ICH_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
# ----------------------------------------------------------------------------
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
# ----------------------------------------------------------------------------
include(FrameworkIlinvaRegistration)
set(oneValueArgs NAME HEADER CLASSNAME)
set(multiValueArgs INTERFACES EXCEPTIONS)
generate_ich_config_file(
  NAME w3wml
  HEADER why3-whyml-ich.hpp
  CONVERTERS why3-whyml-converters.hpp
  CLASSNAME W3WML_ICH
  INTERFACES ccvc4 cz3 saltergo)
# ----------------------------------------------------------------------------
set(LOCAL_ICH_NAME w3wml PARENT_SCOPE)
