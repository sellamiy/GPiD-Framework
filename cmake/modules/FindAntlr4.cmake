# - Try to find Antlr4
# ANTLR4_FOUND
# ANTLR4_EXECUTABLE

find_package(Java COMPONENTS Runtime REQUIRED)

find_program(ANTLR4_EXECUTABLE antlr4)

mark_as_advanced(ANTLR4_EXECUTABLE)
