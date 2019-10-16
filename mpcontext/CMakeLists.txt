# ==============================================================================
# Minpart Target Contexts
# ==============================================================================
include(FrameworkMinpartContextRegistration)
include(FileSystemTools)
# ==============================================================================
subdirlist(LOCAL_MINPART_CONTEXT_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})
foreach(subdir ${LOCAL_MINPART_CONTEXT_DIRECTORIES})
  if (NOT ${subdir} IN_LIST SKIP_MINPART_CONTEXT)
    load_mpcontext_directory(${subdir})
  endif()
endforeach()
# ------------------------------------------------------------------------------
set(MPCONTEXT_STATIC_TARGETS)
set(MPCONTEXT_SHARED_TARGETS)
foreach(context ${MPCONTEXT_TARGETS})
  list(APPEND MPCONTEXT_STATIC_TARGETS ${context}-static)
  list(APPEND MPCONTEXT_SHARED_TARGETS ${context}-shared)
endforeach()
set(MPCONTEXT_TARGETS ${MPCONTEXT_TARGETS} PARENT_SCOPE)
set(MPCONTEXT_STATIC_TARGETS ${MPCONTEXT_STATIC_TARGETS} PARENT_SCOPE)
set(MPCONTEXT_SHARED_TARGETS ${MPCONTEXT_SHARED_TARGETS} PARENT_SCOPE)
# ==============================================================================
