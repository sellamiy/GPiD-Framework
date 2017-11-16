# ==============================================================================
# Solver registration utilities
# ==============================================================================
macro(register_solver_library solver_name solver_includes)
  set(INTERFACE_SOURCES ${ARGN})
  set(INTERFACE_TARGET gpid-${solver_name})
  set(INTERFACE_STATIC_TARGET gpid-${solver_name}-static)
  set(INTERFACE_SHARED_TARGET gpid-${solver_name}-shared)
  add_library(${INTERFACE_STATIC_TARGET} STATIC ${INTERFACE_SOURCES})
  add_library(${INTERFACE_SHARED_TARGET} SHARED ${INTERFACE_SOURCES})
  target_include_directories(${INTERFACE_STATIC_TARGET}
    PUBLIC "${solver_includes}" "${LOCAL_SOLVERS_HEADERS_INCLUDE}")
  target_include_directories(${INTERFACE_SHARED_TARGET}
    PUBLIC "${solver_includes}" "${LOCAL_SOLVERS_HEADERS_INCLUDE}")
  set_target_properties(${INTERFACE_STATIC_TARGET} PROPERTIES
    OUTPUT_NAME ${INTERFACE_TARGET}
    CLEAN_DIRECT_OUTPUT 1)
  set_target_properties(${INTERFACE_SHARED_TARGET} PROPERTIES
    OUTPUT_NAME ${INTERFACE_TARGET}
    VERSION ${VERSION}
    CLEAN_DIRECT_OUTPUT 1)
  target_link_libraries(${INTERFACE_STATIC_TARGET} gpid-core-static)
  target_link_libraries(${INTERFACE_SHARED_TARGET} gpid-core-shared)
  set(SOLVERS_TARGETS ${SOLVERS_TARGETS} ${solver_name} PARENT_SCOPE)
  set(SOLVERS_STATIC_TARGETS ${SOLVERS_STATIC_TARGETS} ${INTERFACE_STATIC_TARGET} PARENT_SCOPE)
  set(SOLVERS_SHARED_TARGETS ${SOLVERS_SHARED_TARGETS} ${INTERFACE_SHARED_TARGET} PARENT_SCOPE)
endmacro()
# ==============================================================================
macro(target_solver_static_libraries solver_name)
  set(INTERFACE_STATIC_TARGET gpid-${solver_name}-static)
  target_link_libraries(${INTERFACE_STATIC_TARGET} ${ARGN})
endmacro()
macro(target_solver_shared_libraries solver_name)
  set(INTERFACE_SHARED_TARGET gpid-${solver_name}-shared)
  target_link_libraries(${INTERFACE_SHARED_TARGET} ${ARGN})
endmacro()
macro(target_solver_libraries solver_name)
  target_solver_static_libraries(${ARGV})
  target_solver_shared_libraries(${ARGV})
endmacro()
# ==============================================================================
macro(target_solver_include_directories solver_name)
  set(INTERFACE_STATIC_TARGET gpid-${solver_name}-static)
  set(INTERFACE_SHARED_TARGET gpid-${solver_name}-shared)
  target_include_directories(${INTERFACE_STATIC_TARGET}
    PUBLIC "${ARGN}")
  target_include_directories(${INTERFACE_SHARED_TARGET}
    PUBLIC "${ARGN}")
endmacro()
# ==============================================================================
macro(generate_solver_interface_header solver_name local_include_dir)
  set(SOLVER_INTERFACE_NAME "${solver_name}")
  set(SOLVER_INTERFACE_HEADER "${LOCAL_SOLVERS_HEADERS_DIR}/${solver_name}.hpp")
  set(SOLVER_ENGINE_HEADER "${local_include_dir}/${solver_name}_engine.hpp")
  set(SOLVER_INPUT_HEADER  "${local_include_dir}/${solver_name}_inputs.hpp")
  set(SOLVER_OUTPUT_HEADER "${local_include_dir}/${solver_name}_outputs.hpp")
  configure_file("${CMAKE_SOURCE_DIR}/framework/gpid/include/solver_interface.hpp.in"
    "${SOLVER_INTERFACE_HEADER}" @ONLY)
  set(SOLVERS_HEADERS ${SOLVERS_HEADERS}
    "${LOCAL_SOLVERS_HEADERS_DIR_RELATIVE}/${solver_name}.hpp" PARENT_SCOPE)
endmacro()
# ==============================================================================
macro(generate_solver_interfaces_global_header)
  set(ALL_SOLVERS_INTERFACE_HEADER "${LOCAL_SOLVERS_HEADERS_DIR}/all.hpp")
  file(WRITE ${ALL_SOLVERS_INTERFACE_HEADER}  "#ifndef GPID_ALL_SOLVERS_INTERFACE_HPP\n")
  file(APPEND ${ALL_SOLVERS_INTERFACE_HEADER} "#define GPID_ALL_SOLVERS_INTERFACE_HPP\n")
  foreach(header ${SOLVERS_HEADERS})
    file(APPEND ${ALL_SOLVERS_INTERFACE_HEADER} "#include<${header}>\n")
  endforeach()
  file(APPEND ${ALL_SOLVERS_INTERFACE_HEADER} "#endif\n")
endmacro()
# ==============================================================================
