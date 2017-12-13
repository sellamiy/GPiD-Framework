# - Try to find tooleval compiler
# TOOLEVALC : compiler executable

find_program(
  TOOLEVALC
  NAMES toolevalc
  DOC "Tool Evaluation Scripts Compiler"
)

if (TOOLEVALC)
  set(TOOLEVAL_FOUND true)

  macro(compile_tooleval_script target_directory script_file required_files)

    get_filename_component(execname "${script_file}" NAME_WE)
    set(target_executable "${target_directory}/${execname}")
    
    add_custom_command(
      OUTPUT  ${target_executable}
      DEPENDS ${script_file} ${required_files}
      COMMAND ${TOOLEVALC} -c ${script_file} -o ${target_executable})
    add_custom_target(${execname} ALL DEPENDS ${target_executable})

  endmacro()
endif()

mark_as_advanced(TOOLEVAL_FOUND TOOLEVALC)
