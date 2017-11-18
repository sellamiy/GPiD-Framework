# ==============================================================================
# Executable utilities packed with the framework
# ==============================================================================
project(gpid-execs LANGUAGES CXX)
# ==============================================================================
# Generate Solver code snippets for executables
# ==============================================================================
include(FrameworkSolverSnippets)
set(SNIPPET_SOLVERS_GTS "")
generate_solver_snippet(${LOCAL_SOLVERS_SNIPPETS_DIR}
  ${LOCAL_SOLVERS_SNIPPETS_CONFIG}
  gts-interfaces.hpp ${SOLVERS_TARGETS})
set(SNIPPET_SOLVERS_GTS ${SNIPPET_SOLVERS_GTS}
  ${CURRENT_SNIPPET_OUTPUT_TARGETS})
generate_solver_snippet(${LOCAL_SOLVERS_SNIPPETS_DIR}
  ${LOCAL_SOLVERS_SNIPPETS_CONFIG}
  gts-executors.hpp  ${SOLVERS_TARGETS})
set(SNIPPET_SOLVERS_GTS ${SNIPPET_SOLVERS_GTS}
  ${CURRENT_SNIPPET_OUTPUT_TARGETS})
add_custom_target(gts-solvers-snippets
  DEPENDS ${SNIPPET_SOLVERS_GTS})
# ==============================================================================
# GTS - an implicate generator
# ==============================================================================
set(GTS_STATIC_LINK_LIBRARIES witchw-static cxxopts)
set(GTS_SHARED_LINK_LIBRARIES witchw-shared cxxopts)
add_executable(gpid-gts "src/gpid-gts.cpp")
add_dependencies(gpid-gts gts-solvers-snippets)
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-gts gpid-solvers-static ${GTS_STATIC_LINK_LIBRARIES})
else()
  target_link_libraries(gpid-gts gpid-solvers-shared ${GTS_SHARED_LINK_LIBRARIES})
endif()
# ==============================================================================
# Split-GTS - single implicate generators linked to specific solver
# ==============================================================================
function(add_split_gts solver)
  set(SGTS_EXECUTABLE_NAME gpid-gts-${solver})
  set(SGTS_SSOLVER_MACRO SINGLE_SOLVER_${solver})
  set(SGTS_STATIC_LINK gpid-${solver}-static)
  set(SGTS_SHARED_LINK gpid-${solver}-shared)
  add_executable(${SGTS_EXECUTABLE_NAME} "src/gpid-gts.cpp")
  add_dependencies(${SGTS_EXECUTABLE_NAME} gts-solvers-snippets)
  target_compile_definitions(${SGTS_EXECUTABLE_NAME} PRIVATE
    SINGLE_SOLVER_ONLY
    ${SGTS_SSOLVER_MACRO})
  if(STATIC_EXECUTABLES)
    target_link_libraries(${SGTS_EXECUTABLE_NAME} ${SGTS_STATIC_LINK} ${GTS_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(${SGTS_EXECUTABLE_NAME} ${SGTS_SHARED_LINK} ${GTS_SHARED_LINK_LIBRARIES})
  endif()
endfunction()

foreach(solver ${SOLVERS_TARGETS})
  add_split_gts(${solver})
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
