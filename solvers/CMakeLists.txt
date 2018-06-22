# ==============================================================================
# GPiD Target solvers
# ==============================================================================
include(FrameworkSolverRegistration)
# ==============================================================================
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
# ------------------------------------------------------------------------------
subdirlist(LOCAL_SOLVER_INTERFACE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
foreach(subdir ${LOCAL_SOLVER_INTERFACE_DIRECTORIES})
  if (NOT ${subdir} IN_LIST SKIP_SOLVER_INTERFACE)
    load_interface_directory(${subdir})
  endif()
endforeach()
# ------------------------------------------------------------------------------
set(SOLVER_STATIC_TARGETS)
set(SOLVER_SHARED_TARGETS)
foreach(interface ${SOLVER_TARGETS})
  list(APPEND SOLVER_STATIC_TARGETS ${interface}-static)
  list(APPEND SOLVER_SHARED_TARGETS ${interface}-shared)
endforeach()
set(SOLVER_TARGETS ${SOLVER_TARGETS} PARENT_SCOPE)
set(SOLVER_STATIC_TARGETS ${SOLVER_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVER_SHARED_TARGETS ${SOLVER_SHARED_TARGETS} PARENT_SCOPE)
# ==============================================================================
