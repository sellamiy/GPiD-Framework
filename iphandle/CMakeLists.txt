# ==============================================================================
# GPiD Ilinva Code Handlers
# ==============================================================================
include(FileSystemTools)
include(FrameworkIlinvaRegistration)
# ==============================================================================
subdirlist(LOCAL_IPH_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
foreach(subdir ${LOCAL_IPH_DIRECTORIES})
  if (NOT ${subdir} IN_LIST SKIP_ILINVA_HANDLER)
    load_iph_directory(${subdir})
  endif()
endforeach()
# ------------------------------------------------------------------------------
set(IPH_STATIC_TARGETS)
set(IPH_SHARED_TARGETS)
foreach(iph ${IPH_TARGETS})
  list(APPEND IPH_STATIC_TARGETS ${iph}-static)
  list(APPEND IPH_SHARED_TARGETS ${iph}-shared)
endforeach()
set(IPH_TARGETS ${IPH_TARGETS} PARENT_SCOPE)
set(IPH_STATIC_TARGETS ${IPH_STATIC_TARGETS} PARENT_SCOPE)
set(IPH_SHARED_TARGETS ${IPH_SHARED_TARGETS} PARENT_SCOPE)
# ==============================================================================
