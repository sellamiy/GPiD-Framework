# ==============================================================================
# Executable utilities packed with the framework
# ==============================================================================
project(gpid-execs LANGUAGES CXX)
# ==============================================================================
# GTS - an implicate generator
# ==============================================================================
set(GTS_STATIC_LINK_LIBRARIES witchw-static cxxopts)
set(GTS_SHARED_LINK_LIBRARIES witchw-shared cxxopts)
add_executable(gpid-gts "src/gpid-gts.cpp")
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-gts gpid-static ${GTS_STATIC_LINK_LIBRARIES})
else()
  target_link_libraries(gpid-gts gpid-shared ${GTS_SHARED_LINK_LIBRARIES})
endif()
# ==============================================================================
# Split-GTS - single implicate generators linked to specific solver
# ==============================================================================
function(add_split_gts exec_name solver_macro static-ass shared-ass)
  add_executable(${exec_name} "src/gpid-gts.cpp")
  target_compile_definitions(${exec_name} PRIVATE
    SINGLE_SOLVER_ONLY
    ${solver_macro})
  if(STATIC_EXECUTABLES)
    target_link_libraries(${exec_name} ${static-ass} ${GTS_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(${exec_name} ${shared-ass} ${GTS_SHARED_LINK_LIBRARIES})
  endif()
endfunction()
if(MINISAT_SOLVER_INTERFACE)
  add_split_gts(gpid-minisat-gts SINGLE_SOLVER_MINISAT gpid-minisat-static gpid-minisat-shared)
endif()
if(CVC4_SOLVER_INTERFACE)
  add_split_gts(gpid-cvc4-gts SINGLE_SOLVER_CVC4 gpid-cvc4-static gpid-cvc4-shared)
endif()
if(Z3_SOLVER_INTERFACE)
  add_split_gts(gpid-z3-gts SINGLE_SOLVER_Z3 gpid-z3-static gpid-z3-shared)
endif()
# ==============================================================================
# Parser - an abducible files parser
# ==============================================================================
add_executable(gpid-parser "src/gpid-parser.cpp")
if(STATIC_EXECUTABLES)
  target_link_libraries(gpid-parser gpid-core-static cxxopts)
else()
  target_link_libraries(gpid-parser gpid-core-shared cxxopts)
endif()
