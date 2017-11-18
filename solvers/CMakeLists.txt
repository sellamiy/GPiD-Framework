# ==============================================================================
# GPiD Target solvers
# ==============================================================================
include(FrameworkSolverRegistration)
include(FrameworkSolverSnippets)
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
# ==============================================================================
subdirlist(SOLVERS_SUBDIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
foreach(solver_subdir ${SOLVERS_SUBDIRECTORIES})
  if (NOT ${solver_subdir} IN_LIST SKIP_SOLVERS)
    message(STATUS "loading solver configuration: ${solver_subdir}")
    add_subdirectory(${solver_subdir})
  endif()
endforeach()
# ==============================================================================
add_library(gpid-solvers-static INTERFACE)
add_library(gpid-solvers-shared INTERFACE)
target_link_libraries(gpid-solvers-static INTERFACE ${SOLVERS_STATIC_TARGETS})
target_link_libraries(gpid-solvers-shared INTERFACE ${SOLVERS_SHARED_TARGETS})

generate_solver_snippet(${LOCAL_SOLVERS_HEADERS_DIR}
  ${LOCAL_SOLVERS_SNIPPETS_CONFIG} interface.hpp ${SOLVERS_TARGETS})
set(SINGLE_SOLVERS_INTERFACE_HEADERS ${CURRENT_SNIPPET_OUTPUT_TARGETS})
set(SINGLE_SOLVERS_INTERFACE_TARGETS "")
foreach(solver ${SOLVERS_TARGETS})
  set(CURRENT_SOLVER_INTERFACE_HEADER
    ${LOCAL_SOLVERS_HEADERS_DIR}/${solver}_interface.hpp)
  set(CURRENT_SOLVER_INTERFACE_TARGET gpid-solvers-headers-${solver})
  set(CURRENT_SOLVER_STATIC_LIBRARY gpid-${solver}-static)
  set(CURRENT_SOLVER_SHARED_LIBRARY gpid-${solver}-shared)
  add_custom_target(${CURRENT_SOLVER_INTERFACE_TARGET}
    DEPENDS ${CURRENT_SOLVER_INTERFACE_HEADER})
  add_dependencies(${CURRENT_SOLVER_STATIC_LIBRARY}
    ${CURRENT_SOLVER_INTERFACE_TARGET})
  add_dependencies(${CURRENT_SOLVER_SHARED_LIBRARY}
    ${CURRENT_SOLVER_INTERFACE_TARGET})
  list(APPEND SINGLE_SOLVERS_INTERFACE_TARGETS
    ${CURRENT_SOLVER_INTERFACE_TARGET})
endforeach()

generate_solver_snippet(${LOCAL_SOLVERS_HEADERS_DIR}
  ${LOCAL_SOLVERS_SNIPPETS_CONFIG} all.hpp ${SOLVERS_TARGETS})
add_custom_target(gpid-solvers-headers-all
  DEPENDS ${CURRENT_SNIPPET_OUTPUT_TARGETS}
  ${SINGLE_SOLVERS_INTERFACE_TARGETS} ${SINGLE_SOLVERS_INTERFACE_HEADERS})

add_dependencies(gpid-solvers-static gpid-solvers-headers-all)
add_dependencies(gpid-solvers-shared gpid-solvers-headers-all)
# ==============================================================================
set(SOLVERS_TARGETS ${SOLVERS_TARGETS} PARENT_SCOPE)
set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} PARENT_SCOPE)
