# - Try to find CVC4
# DOT_EXEC_PATH - Path to dot executable

# Strongly inspired from the Doxygen Dot Finder

file(
  GLOB _Doxygen_GRAPHVIZ_BIN_DIRS
  "$ENV{ProgramFiles}/Graphviz*/bin"
  "$ENV{ProgramFiles${_x86}}/Graphviz*/bin"
)

find_program(
  DOT_EXEC_PATH
  NAMES dot
  PATHS
  ${_Doxygen_GRAPHVIZ_BIN_DIRS}
  "$ENV{ProgramFiles}/ATT/Graphviz/bin"
  "C:/Program Files/ATT/Graphviz/bin"
  [HKEY_LOCAL_MACHINE\\SOFTWARE\\ATT\\Graphviz;InstallPath]/bin
  /Applications/Graphviz.app/Contents/MacOS
  /Applications/Doxygen.app/Contents/Resources
  /Applications/Doxygen.app/Contents/MacOS
  DOC "Dot tool for use with Doxygen"
)
if (DOT_EXEC_PATH)
  set(DOT_FOUND true)
endif()
mark_as_advanced(DOT_FOUND DOT_EXEC_PATH)
