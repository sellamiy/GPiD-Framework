#define GPID_FRAMEWORK__UTIL__ABDPARSER_UTIL_CPP

#include <abdulot/core/memory.hpp>
#include <abdulot/utils/abducibles-utils.hpp>

using namespace snlog;
using namespace abdulot;

extern const std::string abdulot::abducibles_memory_id = "Abducibles";

extern uint32_t abdulot::getAbducibleCount(std::string filename) {
    AbducibleParser parser(filename);
    parser.init();
    if (parser.isValid()) {
        return parser.getAbducibleCount();
    } else {
        throw ParseError("Failed to count abducibles in @file:" + filename);
    }
}

extern void abdulot::loadAbducibles(std::string filename, AbducibleHandler& handler) {
    size_t size = getAbducibleCount(filename);
    handler.allocate(abducibles_memory_id, size);
    std::map<int, int> linker;
    AbducibleParser parser(filename);
    parser.init();
    for (uint32_t i = 0; i < size; i++) {
        if (!parser.isValid()) {
            throw ParseError("Error loading from @file:" + filename);
        }
        handler.handleAbducible(parser.nextAbducible());
    }
}
