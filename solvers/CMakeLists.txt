# ==============================================================================
# GPiD Target solvers
# ==============================================================================
include(FrameworkSolverRegistration)
# ==============================================================================

# ------------------------------------------------------------------------------
macro(subdirlist result curdir)
  file(GLOB children RELATIVE ${curdir} ${curdir}/*)
  set(dirlist "")
  foreach(child ${children})
    if(IS_DIRECTORY ${curdir}/${child})
      list(APPEND dirlist ${child})
    endif()
  endforeach()
  set(${result} ${dirlist})
endmacro()
# ==============================================================================
subdirlist(LOCAL_SOLVER_INTERFACE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
#foreach(subdir ${LOCAL_SOLVER_INTERFACE_DIRECTORIES})
#  if (NOT ${subdir} IN_LIST SKIP_STANDARD_SAL)
#    set(INPUT_SAL_CONFIG_FILE "${CMAKE_CURRENT_SOURCE_DIR}/${subdir}/config.yaml")
#    if (EXISTS ${INPUT_SAL_CONFIG_FILE})
#      set(OUTPUT_SAL_CONFIG_FILE "${LOCAL_SAL_CMAKE_DIR}/${subdir}/CMakeLists.txt")
#      execute_process(
#        COMMAND ${PYTHON_EXECUTABLE} ${SAL_CONFIG_PREPROCESSOR} -d "${SAL_CONFIG_TEMPLATE_DIRECTORY}"
#        -o "${OUTPUT_SAL_CONFIG_FILE}" "${INPUT_SAL_CONFIG_FILE}"
#        RESULT_VARIABLE CONFIG_PREPROCESSING_RESULT)
#      if (NOT ${CONFIG_PREPROCESSING_RESULT} EQUAL 0)
#        message(FATAL_ERROR "Failed to preprocess ${subdir} local interface configuration")
#      endif()
#      add_subdirectory("${LOCAL_SAL_CMAKE_DIR}/${subdir}")
#    endif()
#  endif()
#endforeach()
# ==============================================================================
add_library(gpid-solver-interfaces-static INTERFACE)
add_library(gpid-solver-interfaces-shared INTERFACE)
target_include_directories(gpid-solver-interfaces-static INTERFACE
  ${LOCAL_SOLVER_INTERFACES_INCLUDE})
target_include_directories(gpid-solver-interfaces-shared INTERFACE
  ${LOCAL_SOLVER_INTERFACES_INCLUDE})
target_link_libraries(gpid-solver-interfaces-static INTERFACE ${SOLVER_STATIC_TARGETS})
target_link_libraries(gpid-solver-interfaces-shared INTERFACE ${SOLVER_SHARED_TARGETS})
# ==============================================================================
# TODO: Generate solver interfaces multi headers
# ------------------------------------------------------------------------------
# ------------------------------------------------------------------------------
add_dependencies(gpid-solver-interfaces-static gpid-solver-interfaces-headers)
add_dependencies(gpid-solver-interfaces-shared gpid-solver-interfaces-headers)
# ==============================================================================
set(SOLVER_TARGETS ${SOLVER_TARGETS} PARENT_SCOPE)
set(SOLVER_STATIC_TARGETS ${SOLVER_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVER_SHARED_TARGETS ${SOLVER_SHARED_TARGETS} PARENT_SCOPE)
# ==============================================================================
