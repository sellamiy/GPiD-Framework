# ==============================================================================
# GPiD Ilinva Code Handlers
# ==============================================================================
include(FileSystemTools)
include(FrameworkIlinvaRegistration)
# ==============================================================================
subdirlist(LOCAL_ICH_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
foreach(subdir ${LOCAL_ICH_DIRECTORIES})
  if (NOT ${subdir} IN_LIST SKIP_ILINVA_HANDLER)
    load_ich_directory(${subdir})
  endif()
endforeach()
# ------------------------------------------------------------------------------
set(ICH_STATIC_TARGETS)
set(ICH_SHARED_TARGETS)
foreach(ich ${ICH_TARGETS})
  list(APPEND ICH_STATIC_TARGETS ${ich}-static)
  list(APPEND ICH_SHARED_TARGETS ${ich}-shared)
endforeach()
set(ICH_TARGETS ${ICH_TARGETS} PARENT_SCOPE)
set(ICH_STATIC_TARGETS ${ICH_STATIC_TARGETS} PARENT_SCOPE)
set(ICH_SHARED_TARGETS ${ICH_SHARED_TARGETS} PARENT_SCOPE)
# ==============================================================================
