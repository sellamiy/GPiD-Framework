# *********************************
# Why3 Platform Executable Finder
# *********************************
find_program(
  WHY3_EXECUTABLE
  NAMES why3
  DOC "Why3 Platform"
)

mark_as_advanced(WHY3_EXECUTABLE)
