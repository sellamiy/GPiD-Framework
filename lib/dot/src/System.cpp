#define _DOT_SYSTEM_LIBRARY_
#include <cstdlib>
#include <fstream>
#include <dot/dotcommand.hpp>

#ifdef DOT_FOUND
extern void dot::system::autocompile(Graph& g, std::string filename) {
    std::ofstream temporary(filename + ".dot");
    temporary << g;
    temporary.close();
    std::string command = DOT_EXEC_PATH " -Tsvg -o ";
    command += filename + " " + filename + ".dot";
    std::system(command.c_str());
}
#else
extern void dot::system::autocompile(Graph& g, std::string filename) {
    snlog::l_internal("Dot autocompilation not configured");
}
#endif
