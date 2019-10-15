# ==============================================================================
# Executable utilities packed with the framework
# ==============================================================================
project(abdulot-execs LANGUAGES CXX)
# ==============================================================================
set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
# ==============================================================================
# Generate interfaces code for executables
# ==============================================================================
set(EXEC_CORE_DIR "${CMAKE_SOURCE_DIR}/tools")
# ==============================================================================
include(FrameworkSolverRegistration)
# ------------------------------------------------------------------------------
generate_multi_file(
  "${LOCAL_EXEC_INCLUDE_DIR}/sai/identifiers.hpp"
  "${EXEC_CORE_DIR}/core/templates/identifiers.hpp"
  ${SOLVER_TARGETS})
generate_multi_file(
  "${LOCAL_EXEC_INCLUDE_DIR}/gpid/generators.hpp"
  "${EXEC_CORE_DIR}/gpid/templates/gpid-generators.hpp"
  ${SOLVER_TARGETS})
# ------------------------------------------------------------------------------
include(FrameworkIlinvaRegistration)
# ------------------------------------------------------------------------------
generate_iph_multi_file(
  TARGET "${LOCAL_EXEC_INCLUDE_DIR}/ilinva/generators.hpp"
  TEMPLATE "${EXEC_CORE_DIR}/ilinva/templates/ilinva-generators.hpp"
  IPHANDLERS ${IPH_TARGETS})
# ==============================================================================
set(CORE_STATIC_LINK_LIBRARIES abdulot-static cxxopts Threads::Threads)
set(CORE_SHARED_LINK_LIBRARIES abdulot-shared cxxopts Threads::Threads)
# ------------------------------------------------------------------------------
function(add_split_exec interface name source) # ARGN: Dependencies
  set(SEXEC_EXECUTABLE_NAME ${name}-${interface})
  set(SEXEC_SSOLVER_MACRO SINGLE_SOLVER_${interface})
  string(REGEX REPLACE - _ SEXEC_SSOLVER_MACRO ${SEXEC_SSOLVER_MACRO})
  set(SEXEC_STATIC_LINK ${interface}-static)
  set(SEXEC_SHARED_LINK ${interface}-shared)
  register_executable(${SEXEC_EXECUTABLE_NAME} "${source}")
  add_dependencies(${SEXEC_EXECUTABLE_NAME} ${ARGN})
  target_include_directories(${SEXEC_EXECUTABLE_NAME} PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
  target_compile_definitions(${SEXEC_EXECUTABLE_NAME} PRIVATE
    SINGLE_SOLVER_ONLY
    ${SEXEC_SSOLVER_MACRO})
  if(STATIC_EXECUTABLES)
    target_link_libraries(${SEXEC_EXECUTABLE_NAME} ${SEXEC_STATIC_LINK} ${CORE_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(${SEXEC_EXECUTABLE_NAME} ${SEXEC_SHARED_LINK} ${CORE_SHARED_LINK_LIBRARIES})
  endif()
  install(TARGETS ${SEXEC_EXECUTABLE_NAME} RUNTIME DESTINATION bin)
endfunction()
# ==============================================================================
# GPiD - an implicate generator
# ==============================================================================
if(BUILD_GPID)
  register_executable(gpid "gpid/src/gpid.cpp")
  add_dependencies(gpid identifiers-multi gpid-generators-multi)
  target_include_directories(gpid PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
  if(STATIC_EXECUTABLES)
    target_link_libraries(gpid ${SOLVER_STATIC_TARGETS} ${CORE_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(gpid ${SOLVER_SHARED_TARGETS} ${CORE_SHARED_LINK_LIBRARIES})
  endif()
  install(TARGETS gpid RUNTIME DESTINATION bin)
endif()
# ==============================================================================
# Split-GPiD - single implicate generators linked to specific solver
# ==============================================================================
if(BUILD_GPID)
  foreach(interface ${SOLVER_TARGETS})
    add_split_exec(${interface} "gpid" "gpid/src/gpid.cpp" identifiers-multi gpid-generators-multi)
  endforeach()
endif()
# ==============================================================================
# Ilinvas - a loop invariant generator
# ==============================================================================
if(BUILD_ILINVA)
  foreach(iph ${IPH_TARGETS})
    set(execname ilinva-${iph})
    set(IPH_DEF_MACRO ILINVA_CODE_HANDLER_${iph})
    string(REGEX REPLACE - _ IPH_DEF_MACRO ${IPH_DEF_MACRO})
    set(IPH_SOLVER_MACROS)
    foreach(interface ${SOLVER_TARGETS})
      set(SOLVER_MACRO SOLVER_INTERFACE_${interface})
      string(REGEX REPLACE - _ SOLVER_MACRO ${SOLVER_MACRO})
      list(APPEND IPH_SOLVER_MACROS ${SOLVER_MACRO})
    endforeach()
    register_executable(${execname} "ilinva/src/ilinva.cpp")
    add_dependencies(${execname} identifiers-multi ilinva-generators-multi)
    target_include_directories(${execname} PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
    target_compile_definitions(${execname} PRIVATE ${IPH_DEF_MACRO})
    target_compile_definitions(${execname} PRIVATE ${IPH_SOLVER_MACROS})
    if(STATIC_EXECUTABLES)
      target_link_libraries(${execname}
        ${iph}-static
        ${SOLVER_STATIC_TARGETS}
        ${CORE_STATIC_LINK_LIBRARIES})
    else()
      target_link_libraries(${execname}
        ${iph}-shared
        ${SOLVER_SHARED_TARGETS}
        ${CORE_SHARED_LINK_LIBRARIES})
    endif()
    install(TARGETS ${execname} RUNTIME DESTINATION bin)
    # TODO: Maybe: Split executable solver targets for ilinva
  endforeach()
endif()
# ==============================================================================
# MinPart-SL - SL model minimizer
# ==============================================================================
if(BUILD_MINPART_SL)
  find_package(CVC4)
  if (NOT CVC4_FOUND)
    message(ERROR "CVC4 not found --- cannot build minpart-sl")
  else()
    file(GLOB MINPART_SL_HEADERS "minpart-sl/lib/*.cpp")
    configure_file("${CMAKE_CURRENT_SOURCE_DIR}/minpart-sl/lib/solver-config.hpp.in"
      "${LOCAL_EXEC_INCLUDE_DIR}/minpart-sl/lib/solver-config.hpp")
    add_library(minpart-slcvc-context STATIC ${MINPART_SL_HEADERS})
    target_include_directories(minpart-slcvc-context
      PUBLIC ${CVC4_INCLUDE_DIR} "minpart-sl/lib" "${LOCAL_EXEC_INCLUDE_DIR}/minpart-sl/lib")
    set_target_properties(minpart-slcvc-context PROPERTIES
      OUTPUT_NAME minpart-slcvc-context
      CLEAN_DIRECT_OUTPUT 1)
    target_link_libraries(minpart-slcvc-context minpart-static lisptp-static ${CVC4_LIBRARIES} cxxopts)

    register_executable(minpart-sl "minpart-sl/src/minpart-sl.cpp")
    target_link_libraries(minpart-sl minpart-slcvc-context)

    install(TARGETS minpart-slcvc-context minpart-sl
      ARCHIVE DESTINATION lib
      LIBRARY DESTINATION lib
      RUNTIME DESTINATION bin)
  endif()
endif()
# ==============================================================================
