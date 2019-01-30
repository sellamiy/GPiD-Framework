# ==============================================================================
# Why3 - WhyML - C++ Wrapper ICH
# ==============================================================================
# TODO: Find Why3 and related; Do the following only if found; else message
# TODO: include_directories(**Why3 Stuff**)
# ----------------------------------------------------------------------------
file(GLOB ICH_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
file(GLOB ICH_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
# ----------------------------------------------------------------------------
add_library(why3-whyml-ich-static STATIC ${ICH_SOURCES})
add_library(why3-whyml-ich-shared SHARED ${ICH_SOURCES})
target_include_directories(why3-whyml-ich-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories(why3-whyml-ich-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
set_target_properties(why3-whyml-ich-static PROPERTIES
  OUTPUT_NAME why3-whyml-ich
  CLEAN_DIRECT_OUTPUT 1)
set_target_properties(why3-whyml-ich-shared PROPERTIES
  OUTPUT_NAME why3-whyml-ich
  CLEAN_DIRECT_OUTPUT 1)
target_link_libraries(why3-whyml-ich-static gpid-core-static why3cpp-static)
target_link_libraries(why3-whyml-ich-shared gpid-core-shared why3cpp-shared)
# ----------------------------------------------------------------------------
include(FrameworkIlinvaRegistration)
set(oneValueArgs NAME HEADER CLASSNAME)
set(multiValueArgs INTERFACES EXCEPTIONS)
generate_ich_config_file(
  NAME why3-whyml-ich
  HEADER why3-whyml-ich.hpp
  CONVERTERS why3-whyml-converters.hpp
  CLASSNAME W3WML_ICH
  INTERFACES lcvc4 ccvc4 lz3 cz3)
# ----------------------------------------------------------------------------
set(LOCAL_ICH_NAME why3-whyml-ich PARENT_SCOPE)
