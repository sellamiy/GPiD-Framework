#define LIB_LCDOT__SYSTEM_CPP
#include <cstdlib>
#include <fstream>
#include <snlog/snlog.hpp>
#include <lcdot/dotcommand.hpp>

#ifdef DOT_FOUND
extern void lcdot::system::autocompile(std::string source, std::string target) {
    std::string command = DOT_EXEC_PATH " -Tsvg -o ";
    command += target + " " + source;
    int ret = std::system(command.c_str());
    snlog::t_error(ret != 0, "Dot autocompilation returned non 0");
}
#else
extern void lcdot::system::autocompile(std::string, std::string) {
    snlog::l_internal("Dot autocompilation not configured");
}
#endif