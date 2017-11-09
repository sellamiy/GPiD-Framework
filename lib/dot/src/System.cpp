#define _DOT_SYSTEM_LIBRARY_
#include <cstdlib>
#include <fstream>
#include <dot/dotcommand.hpp>

#ifdef DOT_FOUND
extern void dot::system::autocompile(std::string source, std::string target) {
    std::string command = DOT_EXEC_PATH " -Tsvg -o ";
    command += target + " " + source;
    std::system(command.c_str());
}
#else
#include <snlog/snlog.hpp>
extern void dot::system::autocompile(std::string, std::string) {
    snlog::l_internal("Dot autocompilation not configured");
}
#endif
