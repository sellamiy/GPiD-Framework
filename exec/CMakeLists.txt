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
if(MINISAT_SOLVER_INTERFACE)
  add_executable(gpid-minisat-gts "src/gpid-gts.cpp")
  target_compile_definitions(gpid-minisat-gts PRIVATE
    SINGLE_SOLVER_ONLY
    SINGLE_SOLVER_MINISAT)
  if(STATIC_EXECUTABLES)
    target_link_libraries(gpid-minisat-gts gpid-minisat-static ${GTS_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(gpid-minisat-gts gpid-minisat-shared ${GTS_SHARED_LINK_LIBRARIES})
  endif()
endif()
if(CVC4_SOLVER_INTERFACE)
  add_executable(gpid-cvc4-gts "src/gpid-gts.cpp")
  target_compile_definitions(gpid-cvc4-gts PRIVATE
    SINGLE_SOLVER_ONLY
    SINGLE_SOLVER_CVC4)
  if(STATIC_EXECUTABLES)
    target_link_libraries(gpid-cvc4-gts gpid-cvc4-static ${GTS_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(gpid-cvc4-gts gpid-cvc4-shared ${GTS_SHARED_LINK_LIBRARIES})
  endif()
endif()
if(Z3_SOLVER_INTERFACE)
  add_executable(gpid-z3-gts "src/gpid-gts.cpp")
  target_compile_definitions(gpid-z3-gts PRIVATE
    SINGLE_SOLVER_ONLY
    SINGLE_SOLVER_Z3)
  if(STATIC_EXECUTABLES)
    target_link_libraries(gpid-z3-gts gpid-z3-static ${GTS_STATIC_LINK_LIBRARIES})
  else()
    target_link_libraries(gpid-z3-gts gpid-z3-shared ${GTS_SHARED_LINK_LIBRARIES})
  endif()
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
