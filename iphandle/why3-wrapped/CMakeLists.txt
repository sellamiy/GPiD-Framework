# ==============================================================================
# Why3 - WhyML - C++ Wrapper IPH
# ==============================================================================
find_package(Why3 1.0.0)
# TODO: include_directories(**Why3 Stuff**)
# ------------------------------------------------------------------------------
if (NOT Why3_FOUND)
  message(WARNING "Why3 not found")
  set(LOCAL_IPH_NAME "" PARENT_SCOPE)
else ()
  file(GLOB IPH_HEADERS "${CMAKE_CURRENT_SOURCE_DIR}/include/*.hpp")
  file(GLOB IPH_SOURCES "${CMAKE_CURRENT_SOURCE_DIR}/src/*.cpp")
  # --------------------------------------------------------------------------
  add_library(why3-wrapped-static STATIC ${IPH_SOURCES})
  add_library(why3-wrapped-shared SHARED ${IPH_SOURCES})
  target_include_directories(why3-wrapped-static PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  target_include_directories(why3-wrapped-shared PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
  set_target_properties(why3-wrapped-static PROPERTIES
    OUTPUT_NAME why3-wrapped
    CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(why3-wrapped-shared PROPERTIES
    OUTPUT_NAME why3-wrapped
    CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(why3-wrapped-static abdulot-static why3cpp-static)
  target_link_libraries(why3-wrapped-shared abdulot-shared why3cpp-shared)
  # --------------------------------------------------------------------------
  include(FrameworkIlinvaRegistration)
  set(WHY3_HANDLED_INTERFACES ccvc4 cz3 saltergo)
  set(WHY3_NOT_AVAILABLE)
  foreach(interface ${WHY3_HANDLED_INTERFACES})
    list(FIND SOLVER_TARGETS ${interface} DV_DUMMY)
    if (${DV_DUMMY} LESS 0)
      list(APPEND WHY3_NOT_AVAILABLE ${interface})
    endif()
  endforeach()
  if (WHY3_NOT_AVAILABLE)
    list(REMOVE_ITEM WHY3_HANDLED_INTERFACES ${WHY3_NOT_AVAILABLE})
  endif()
  generate_iph_config_file(
    NAME why3-wrapped
    HEADER why3-wrapped-iph.hpp
    CONVERTERS why3-conversion-wrappers.hpp
    CLASSNAME Why3_IPH
    INTERFACES ${WHY3_HANDLED_INTERFACES})
  # --------------------------------------------------------------------------
  set(LOCAL_IPH_NAME why3-wrapped PARENT_SCOPE)
endif()
