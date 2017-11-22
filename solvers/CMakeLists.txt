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
target_include_directories(gpid-solvers-static INTERFACE
  ${LOCAL_SOLVERS_HEADERS_INCLUDE} ${LOCAL_SOLVERS_SNIPPETS_INCLUDE} ${LOCAL_SOLVERS_INTERFACES_INCLUDE})
target_include_directories(gpid-solvers-shared INTERFACE
  ${LOCAL_SOLVERS_HEADERS_INCLUDE} ${LOCAL_SOLVERS_SNIPPETS_INCLUDE} ${LOCAL_SOLVERS_INTERFACES_INCLUDE})
target_link_libraries(gpid-solvers-static INTERFACE ${SOLVERS_STATIC_TARGETS})
target_link_libraries(gpid-solvers-shared INTERFACE ${SOLVERS_SHARED_TARGETS})

generate_solver_snippet(${LOCAL_SOLVERS_HEADERS_DIR}
  ${LOCAL_SOLVERS_SNIPPETS_CONFIG} all.hpp ${SOLVERS_TARGETS})
add_custom_target(gpid-solvers-headers-all
  DEPENDS ${CURRENT_SNIPPET_OUTPUT_TARGETS}
  ${SOLVERS_INTERFACE_TARGETS} ${SOLVERS_INTERFACE_HEADERS})

add_dependencies(gpid-solvers-static gpid-solvers-headers-all)
add_dependencies(gpid-solvers-shared gpid-solvers-headers-all)
# ==============================================================================
set(SOLVERS_TARGETS ${SOLVERS_TARGETS} PARENT_SCOPE)
set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} PARENT_SCOPE)
set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} PARENT_SCOPE)
