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
file(COPY ${CMAKE_CURRENT_SOURCE_DIR}/gpid/include/version.hpp
  DESTINATION ${FRAMEWORK_CHEADERS_DIRECTORY}/gpid/)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/src/config/version.cpp.in
  ${FRAMEWORK_CSOURCES_DIRECTORY}/config/version.cpp)

# ==============================================================================
# Locating and selecting library sources
# ==============================================================================
file(GLOB LIBGPID_SOURCES
  "${CMAKE_CURRENT_SOURCE_DIR}/src/*/*.cpp"
  "${FRAMEWORK_CSOURCES_DIRECTORY}/*/*.cpp")

if(NOT TRUE_SOLVER_INTERFACE)
  file(GLOB TRUESOLVER_SOURCES
    "${CMAKE_CURRENT_SOURCE_DIR}/src/*/truesolver*.cpp"
    "${FRAMEWORK_CONF_SOURCE_DIR}/*/truesolver*.cpp")
  foreach(filename ${TRUESOLVER_SOURCES})
    list(REMOVE_ITEM LIBGPID_SOURCES ${filename})
  endforeach()
endif()

if(NOT MINISAT_SOLVER_INTERFACE)
  file(GLOB MINISAT_SOURCES
    "${CMAKE_CURRENT_SOURCE_DIR}/src/*/minisat*.cpp"
    "${FRAMEWORK_CONF_SOURCE_DIR}/*/minisat*.cpp")
  foreach(filename ${MINISAT_SOURCES})
    list(REMOVE_ITEM LIBGPID_SOURCES ${filename})
  endforeach()
endif()

if(NOT CVC4_SOLVER_INTERFACE)
  file(GLOB CVC4_SOURCES
    "${CMAKE_CURRENT_SOURCE_DIR}/src/*/cvc4*.cpp"
    "${FRAMEWORK_CONF_SOURCE_DIR}/*/cvc4*.cpp")
  foreach(filename ${CVC4_SOURCES})
    list(REMOVE_ITEM LIBGPID_SOURCES ${filename})
  endforeach()
endif()

if(NOT Z3_SOLVER_INTERFACE)
  file(GLOB Z3_SOURCES
    "${CMAKE_CURRENT_SOURCE_DIR}/src/*/z3*.cpp"
    "${FRAMEWORK_CONF_SOURCE_DIR}/*/z3*.cpp")
  foreach(filename ${Z3_SOURCES})
    list(REMOVE_ITEM LIBGPID_SOURCES ${filename})
  endforeach()
endif()

if(NOT GPID_INSTRUMENTATION)
  file(GLOB INST_SOURCES
    "${CMAKE_CURRENT_SOURCE_DIR}/src/instrument/*.cpp"
    "${FRAMEWORK_CONF_SOURCE_DIR}/instrument/*.cpp")
  foreach(filename ${INST_SOURCES})
    list(REMOVE_ITEM LIBGPID_SOURCES ${filename})
  endforeach()
endif()

# ==============================================================================
# Library target definition
# ==============================================================================
add_library(gpid STATIC ${LIBGPID_SOURCES})

target_include_directories(gpid
  PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}" "${FRAMEWORK_CHEADERS_DIRECTORY}"
  PRIVATE "${FRAMEWORK_CSOURCES_DIRECTORY}")

target_link_libraries(gpid snlog starray dot ugly)

if(MINISAT_SOLVER_INTERFACE)
  target_link_libraries(gpid minisat-lib-shared ${ZLIB_LIBRARY})
endif()
if(CVC4_SOLVER_INTERFACE)
  target_link_libraries(gpid cvc4 cvc4parser)
endif()
if(Z3_SOLVER_INTERFACE)
  target_link_libraries(gpid ${Z3_LIBRARIES})
endif()
