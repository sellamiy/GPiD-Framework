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
generate_ich_multi_file(
  TARGET "${LOCAL_EXEC_INCLUDE_DIR}/ilinva/generators.hpp"
  TEMPLATE "${EXEC_CORE_DIR}/ilinva/templates/ilinva-generators.hpp"
  ICHANDLERS ${ICH_TARGETS})
# ==============================================================================
set(CORE_STATIC_LINK_LIBRARIES abdulot-static cxxopts Threads::Threads)
set(CORE_SHARED_LINK_LIBRARIES abdulot-shared cxxopts Threads::Threads)
# ------------------------------------------------------------------------------
function(add_split_exec interface name source) # ARGN: Dependencies
  set(SEXEC_EXECUTABLE_NAME ${name}-${interface})
  set(SEXEC_SSOLVER_MACRO SINGLE_SOLVER_${interface})
  string(REGEX REPLACE - _tm_ SEXEC_SSOLVER_MACRO ${SEXEC_SSOLVER_MACRO})
  set(SEXEC_STATIC_LINK ${interface}-static)
  set(SEXEC_SHARED_LINK ${interface}-shared)
  add_executable(${SEXEC_EXECUTABLE_NAME} "${source}")
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
# ImpGen - an implicate generator
# ==============================================================================
add_executable(gpid "gpid/src/gpid.cpp")
add_dependencies(gpid identifiers-multi gpid-generators-multi)
target_include_directories(gpid PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid ${SOLVER_STATIC_TARGETS} ${CORE_STATIC_LINK_LIBRARIES})
else()
  target_link_libraries(gpid ${SOLVER_SHARED_TARGETS} ${CORE_SHARED_LINK_LIBRARIES})
endif()
install(TARGETS gpid RUNTIME DESTINATION bin)
# ==============================================================================
# Split-ImpGen - single implicate generators linked to specific solver
# ==============================================================================
foreach(interface ${SOLVER_TARGETS})
  add_split_exec(${interface} "gpid" "gpid/src/gpid.cpp" identifiers-multi gpid-generators-multi)
endforeach()
# ==============================================================================
# Ilinvas - a loop invariant generator
# ==============================================================================
foreach(ich ${ICH_TARGETS})
  set(execname ilinva-${ich})
  set(ICH_DEF_MACRO ILINVA_CODE_HANDLER_${ich})
  string(REGEX REPLACE - _tm_ ICH_DEF_MACRO ${ICH_DEF_MACRO})
  add_executable(${execname} "ilinva/src/ilinva.cpp")
  add_dependencies(${execname} identifiers-multi ilinva-generators-multi)
  target_include_directories(${execname} PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
  target_compile_definitions(${execname} PRIVATE ${ICH_DEF_MACRO})
  if(STATIC_EXECUTABLES)
    target_link_libraries(${execname}
      ${ich}-static
      ${SOLVER_STATIC_TARGETS}
      ${CORE_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(${execname}
      ${ich}-shared
      ${SOLVER_SHARED_TARGETS}
      ${CORE_SHARED_LINK_LIBRARIES})
  endif()
  install(TARGETS ${execname} RUNTIME DESTINATION bin)
  # TODO: Maybe: Split executable solver targets for ilinva
endforeach()