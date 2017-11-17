# ==============================================================================
# GPiD Target solvers
# ==============================================================================
include(FrameworkSolverRegistration)
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
subdirlist(SOLVERS_SUBDIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
foreach(solver_subdir ${SOLVERS_SUBDIRECTORIES})
  message(STATUS "loading solver configuration: ${solver_subdir}")
  add_subdirectory(${solver_subdir})
endforeach()
# ==============================================================================
add_library(gpid-solvers-static INTERFACE)
add_library(gpid-solvers-shared INTERFACE)
target_link_libraries(gpid-solvers-static INTERFACE ${SOLVERS_STATIC_TARGETS})
target_link_libraries(gpid-solvers-shared INTERFACE ${SOLVERS_SHARED_TARGETS})
generate_solver_interfaces_global_header()
# ==============================================================================
set(SOLVERS_TARGETS ${SOLVERS_TARGETS} PARENT_SCOPE)
set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} PARENT_SCOPE)
