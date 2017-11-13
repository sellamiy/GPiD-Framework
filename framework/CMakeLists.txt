# ==============================================================================
# GPiD Framework library target configuration
# ==============================================================================
project(libgpid LANGUAGES CXX)
# ==============================================================================
# Files configuration
# ==============================================================================
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/config.hpp.in
  ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/config.hpp)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/gpid.hpp.in
  ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/gpid.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/gpid.minisat.hpp.in
  ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/gpid.minisat.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/gpid.cvc4.hpp.in
  ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/gpid.cvc4.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/gpid.z3.hpp.in
  ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/gpid.z3.hpp)
configure_file(${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/gpid.all.hpp.in
  ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/gpid.all.hpp)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/src/config/version.cpp.in
  ${FRAMEWORK_CSOURCES_DIRECTORY}/config/version.cpp)
file(COPY ${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/version.hpp
  DESTINATION ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/)

# ==============================================================================
# Locating and selecting library sources
# ==============================================================================
file(GLOB SRC_GPID_CORE
  "${FRAMEWORK_CSOURCES_DIRECTORY}/config/*.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/util/*.cpp"
)

if(GPID_INSTRUMENTATION)
  file(GLOB SRC_GPID_INSTRUMENT
    "${CMAKE_CURRENT_SOURCE_DIR}/src/instrument/*.cpp"
    "${FRAMEWORK_CONF_SOURCE_DIR}/instrument/*.cpp"
  )
endif()

if(TRUE_SOLVER_INTERFACE)
  file(GLOB SRC_GPID_TRUESOLVER
    "${CMAKE_CURRENT_SOURCE_DIR}/src/misc/truesolver_algorithms.cpp"
  )
endif()

if(MINISAT_SOLVER_INTERFACE)
  file(GLOB SRC_GPID_MINISAT
    "${CMAKE_CURRENT_SOURCE_DIR}/src/propositional/minisat*.cpp"
  )
endif()

if(CVC4_SOLVER_INTERFACE)
  file(GLOB SRC_GPID_CVC4
    "${CMAKE_CURRENT_SOURCE_DIR}/src/smt/cvc4*.cpp"
  )
endif()

if(Z3_SOLVER_INTERFACE)
  file(GLOB SRC_GPID_Z3
    "${CMAKE_CURRENT_SOURCE_DIR}/src/smt/z3*.cpp"
  )
endif()

# ==============================================================================
# Library target definition
# ==============================================================================
function (register_gpid_library lname staticname sharedname)
  add_library(${staticname} STATIC ${ARGN})
  add_library(${sharedname} SHARED ${ARGN})
  target_include_directories(${staticname}
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${FRAMEWORK_CHEADERS_DIRECTORY}"
    PRIVATE "${FRAMEWORK_CSOURCES_DIRECTORY}")
  target_include_directories(${sharedname}
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${FRAMEWORK_CHEADERS_DIRECTORY}"
    PRIVATE "${FRAMEWORK_CSOURCES_DIRECTORY}")
  set_target_properties(${staticname} PROPERTIES OUTPUT_NAME ${lname} CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(${sharedname} PROPERTIES
    OUTPUT_NAME ${lname}
    VERSION ${VERSION}
    CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(${staticname} starray-static)
  target_link_libraries(${sharedname} starray-shared)
  set(FRAMEWORK_STATIC_LIBS ${FRAMEWORK_STATIC_LIBS} ${staticname} PARENT_SCOPE)
  set(FRAMEWORK_SHARED_LIBS ${FRAMEWORK_SHARED_LIBS} ${sharedname} PARENT_SCOPE)
endfunction()

register_gpid_library(gpid-core
  gpid-core-static gpid-core-shared
  ${SRC_GPID_CORE} ${SRC_GPID_INSTRUMENT})
target_link_libraries(gpid-core-static snlog)
target_link_libraries(gpid-core-shared snlog)
if(GPID_INSTRUMENTATION)
  target_link_libraries(gpid-core-static dot-static)
  target_link_libraries(gpid-core-shared dot-shared)
endif()

function (register_gpid_solver_library lname staticname sharedname)
  register_gpid_library(${ARGV})
  target_link_libraries(${staticname} gpid-core-static)
  target_link_libraries(${sharedname} gpid-core-shared)
  set(FRAMEWORK_STATIC_LIBS ${FRAMEWORK_STATIC_LIBS} PARENT_SCOPE)
  set(FRAMEWORK_SHARED_LIBS ${FRAMEWORK_SHARED_LIBS} PARENT_SCOPE)
endfunction()

if(TRUE_SOLVER_INTERFACE)
  register_gpid_solver_library(gpid-truesolver
    gpid-truesolver-static gpid-truesolver-shared
    ${SRC_GPID_TRUESOLVER})
endif()
if(MINISAT_SOLVER_INTERFACE)
  register_gpid_solver_library(gpid-minisat
    gpid-minisat-static gpid-minisat-shared
    ${SRC_GPID_MINISAT})
  target_link_libraries(gpid-minisat-static ugly minisat-lib-static )
  target_link_libraries(gpid-minisat-shared ugly minisat-lib-shared )
endif()
if(CVC4_SOLVER_INTERFACE)
  register_gpid_solver_library(gpid-cvc4
    gpid-cvc4-static gpid-cvc4-shared
    ${SRC_GPID_CVC4})
  target_link_libraries(gpid-cvc4-static cvc4 cvc4parser)
  target_link_libraries(gpid-cvc4-shared cvc4 cvc4parser)
endif()
if(Z3_SOLVER_INTERFACE)
  register_gpid_solver_library(gpid-z3
    gpid-z3-static gpid-z3-shared
    ${SRC_GPID_Z3})
  target_link_libraries(gpid-z3-static ${Z3_LIBRARIES})
  target_link_libraries(gpid-z3-shared ${Z3_LIBRARIES})
endif()

add_library(gpid-static INTERFACE)
add_library(gpid-shared INTERFACE)
target_link_libraries(gpid-static INTERFACE ${FRAMEWORK_STATIC_LIBS})
target_link_libraries(gpid-shared INTERFACE ${FRAMEWORK_SHARED_LIBS})
