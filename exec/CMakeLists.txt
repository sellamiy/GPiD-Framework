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
include(FrameworkSolverRegistration)
# ------------------------------------------------------------------------------
set(EXEC_TEMPLATES_DIR "${CMAKE_SOURCE_DIR}/exec/templates")
set(IMPGEN_INCLUDE_TEMPLATES "sai/identifiers.hpp" "sai/impgen-executors.hpp")
set(IMPGEN_SOURCES_TEMPLATES)
set(IMPGEN_PREPROCESSED_FILES)
# ------------------------------------------------------------------------------
foreach(template_name ${IMPGEN_INCLUDE_TEMPLATES})
  set(template_source "${EXEC_TEMPLATES_DIR}/${template_name}")
  set(template_target "${LOCAL_EXEC_INCLUDE_DIR}/${template_name}")
  generate_multi_file("${template_target}" "${template_source}" ${SOLVER_TARGETS})
  list(APPEND IMPGEN_PREPROCESSED_FILES "${template_target}")
endforeach()
foreach(template_name ${IMPGEN_SOURCES_TEMPLATES})
  set(template_source "${EXEC_TEMPLATES_DIR}/src/${template_name}")
  set(template_target "${LOCAL_EXEC_SOURCES_DIR}/src/${template_name}")
  generate_multi_file("${template_target}" "${template_source}" ${SOLVER_TARGETS})
  list(APPEND IMPGEN_PREPROCESSED_FILES "${template_target}")
endforeach()
# ------------------------------------------------------------------------------
add_custom_target(impgen-preprocessed-files DEPENDS ${IMPGEN_PREPROCESSED_FILES})
# ==============================================================================
# ImpGen - an implicate generator
# ==============================================================================
set(IMPGEN_STATIC_LINK_LIBRARIES gpid-core-static witchw-static cxxopts Threads::Threads)
set(IMPGEN_SHARED_LINK_LIBRARIES gpid-core-shared witchw-shared cxxopts Threads::Threads)
add_executable(gpid-impgen "src/gpid-impgen.cpp")
add_dependencies(gpid-impgen impgen-preprocessed-files)
target_include_directories(gpid-impgen PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-impgen gpid-solver-interfaces-static ${IMPGEN_STATIC_LINK_LIBRARIES})
else()
  target_link_libraries(gpid-impgen gpid-solver-interfaces-shared ${IMPGEN_SHARED_LINK_LIBRARIES})
endif()
install(TARGETS gpid-impgen RUNTIME DESTINATION bin)
# ==============================================================================
# Split-IMPGEN - single implicate generators linked to specific solver
# ==============================================================================
function(add_split_impgen interface)
  set(SIMPGEN_EXECUTABLE_NAME gpid-impgen-${interface})
  set(SIMPGEN_SSOLVER_MACRO SINGLE_SOLVER_${interface})
  set(SIMPGEN_STATIC_LINK gpid-${interface}-si-static)
  set(SIMPGEN_SHARED_LINK gpid-${interface}-si-shared)
  add_executable(${SIMPGEN_EXECUTABLE_NAME} "src/gpid-impgen.cpp")
  add_dependencies(${SIMPGEN_EXECUTABLE_NAME} impgen-preprocessed-files)
  target_include_directories(${SIMPGEN_EXECUTABLE_NAME} PRIVATE ${LOCAL_EXEC_INCLUDE_DIR})
  target_compile_definitions(${SIMPGEN_EXECUTABLE_NAME} PRIVATE
    SINGLE_SOLVER_ONLY
    ${SIMPGEN_SSOLVER_MACRO})
  if(STATIC_EXECUTABLES)
    target_link_libraries(${SIMPGEN_EXECUTABLE_NAME} ${SIMPGEN_STATIC_LINK} ${IMPGEN_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(${SIMPGEN_EXECUTABLE_NAME} ${SIMPGEN_SHARED_LINK} ${IMPGEN_SHARED_LINK_LIBRARIES})
  endif()
  install(TARGETS ${SIMPGEN_EXECUTABLE_NAME} RUNTIME DESTINATION bin)
endfunction()

foreach(interface ${SOLVER_TARGETS})
  add_split_impgen(${interface})
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
