# ==============================================================================
# Executable utilities packed with the framework
# ==============================================================================
project(gpid-execs LANGUAGES CXX)
# ==============================================================================
set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
# ==============================================================================
# Generate interfaces code for executables
# ==============================================================================
set(EXEC_TEMPLATES_DIR "${CMAKE_SOURCE_DIR}/exec/templates")
# ==============================================================================
include(FrameworkSolverRegistration)
# ------------------------------------------------------------------------------
set(EXEC_INCLUDE_TEMPLATES "sai/identifiers.hpp" "sai/impgen-executors.hpp")
set(EXEC_SOURCES_TEMPLATES)
set(EXEC_PREPROCESSED_TARGETS)
# ------------------------------------------------------------------------------
foreach(template_name ${EXEC_INCLUDE_TEMPLATES})
  set(template_source "${EXEC_TEMPLATES_DIR}/${template_name}")
  set(template_target "${LOCAL_EXEC_INCLUDE_DIR}/${template_name}")
  get_filename_component(template_info "${template_target}" NAME_WE)
  generate_multi_file("${template_target}" "${template_source}" ${SOLVER_TARGETS})
  list(APPEND EXEC_PREPROCESSED_TARGETS ${template_info}-multi)
endforeach()
foreach(template_name ${EXEC_SOURCES_TEMPLATES})
  set(template_source "${EXEC_TEMPLATES_DIR}/src/${template_name}")
  set(template_target "${LOCAL_EXEC_SOURCES_DIR}/src/${template_name}")
  get_filename_component(template_info "${template_target}" NAME_WE)
  generate_multi_file("${template_target}" "${template_source}" ${SOLVER_TARGETS})
  list(APPEND EXEC_PREPROCESSED_TARGETS ${template_info}-multi)
endforeach()
# ==============================================================================
include(FrameworkIlinvaRegistration)
# ------------------------------------------------------------------------------
set(ILINVA_INCLUDE_TEMPLATES "ilinva/executors.hpp")
set(ILINVA_SOURCES_TEMPLATES)
set(ILINVA_PREPROCESSED_TARGETS "identifiers-multi") # Note: sai/identifiers template required
# ------------------------------------------------------------------------------
foreach(template_name ${ILINVA_INCLUDE_TEMPLATES})
  set(template_source "${EXEC_TEMPLATES_DIR}/${template_name}")
  set(template_target "${LOCAL_EXEC_INCLUDE_DIR}/${template_name}")
  get_filename_component(template_info "${template_target}" NAME_WE)
  generate_ich_multi_file(TARGET "${template_target}" TEMPLATE "${template_source}"
    ICHANDLERS ${ICH_TARGETS})
  list(APPEND ILINVA_PREPROCESSED_TARGETS ${template_info}-multi)
endforeach()
foreach(template_name ${ILINVA_SOURCES_TEMPLATES})
  set(template_source "${EXEC_TEMPLATES_DIR}/src/${template_name}")
  set(template_target "${LOCAL_EXEC_SOURCES_DIR}/src/${template_name}")
  get_filename_component(template_info "${template_target}" NAME_WE)
  generate_ich_multi_file(TARGET "${template_target}" TEMPLATE "${template_source}"
    ICHANDLERS ${ICH_TARGETS})
  list(APPEND ILINVA_PREPROCESSED_TARGETS ${template_info}-multi)
endforeach()
# ==============================================================================
set(CORE_STATIC_LINK_LIBRARIES gpid-core-static cxxopts Threads::Threads)
set(CORE_SHARED_LINK_LIBRARIES gpid-core-shared cxxopts Threads::Threads)
# ------------------------------------------------------------------------------
function(add_split_exec interface name source)
  set(SEXEC_EXECUTABLE_NAME gpid-${name}-${interface})
  set(SEXEC_SSOLVER_MACRO SINGLE_SOLVER_${interface})
  string(REGEX REPLACE - _tm_ SEXEC_SSOLVER_MACRO ${SEXEC_SSOLVER_MACRO})
  set(SEXEC_STATIC_LINK ${interface}-static)
  set(SEXEC_SHARED_LINK ${interface}-shared)
  add_executable(${SEXEC_EXECUTABLE_NAME} "${source}")
  add_dependencies(${SEXEC_EXECUTABLE_NAME} ${EXEC_PREPROCESSED_TARGETS})
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
add_executable(gpid-impgen "src/gpid-impgen.cpp")
add_dependencies(gpid-impgen ${EXEC_PREPROCESSED_TARGETS})
target_include_directories(gpid-impgen PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-impgen ${SOLVER_STATIC_TARGETS} ${CORE_STATIC_LINK_LIBRARIES})
else()
  target_link_libraries(gpid-impgen ${SOLVER_SHARED_TARGETS} ${CORE_SHARED_LINK_LIBRARIES})
endif()
install(TARGETS gpid-impgen RUNTIME DESTINATION bin)
# ==============================================================================
# Split-ImpGen - single implicate generators linked to specific solver
# ==============================================================================
foreach(interface ${SOLVER_TARGETS})
  add_split_exec(${interface} "impgen" "src/gpid-impgen.cpp")
endforeach()
# ==============================================================================
# Parser - an abducible files parser
# ==============================================================================
add_executable(gpid-parser "src/gpid-parser.cpp")
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-parser gpid-core-static cxxopts)
else()
  target_link_libraries(gpid-parser gpid-core-shared cxxopts)
endif()
install(TARGETS gpid-parser RUNTIME DESTINATION bin)
# ==============================================================================
# Ilinvas - a loop invariant generator
# ==============================================================================
foreach(ich ${ICH_TARGETS})
  set(execname gpid-ilinva-${ich})
  set(ICH_DEF_MACRO ILINVA_CODE_HANDLER_${ich})
  string(REGEX REPLACE - _tm_ ICH_DEF_MACRO ${ICH_DEF_MACRO})
  add_executable(${execname} "src/gpid-ilinva.cpp")
  add_dependencies(${execname} ${ILINVA_PREPROCESSED_TARGETS})
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
