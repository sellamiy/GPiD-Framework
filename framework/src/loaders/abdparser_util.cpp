#define GPID_FRAMEWORK__UTIL__ABDPARSER_UTIL_CPP

#include <gpid/core/memory.hpp>
#include <gpid/loaders/abdparseutils.hpp>

using namespace snlog;
using namespace gpid;

extern const std::string gpid::abducibles_memory_id = "Abducibles";

extern uint32_t gpid::getAbducibleCount(std::string filename) {
    AbducibleParser parser(filename);
    parser.init();
    if (parser.isOk()) {
        return parser.getAbducibleCount();
    } else {
        throw ParseError("Failed to count abducibles in @file:" + filename);
    }
}

extern void gpid::loadAbducibles(std::string filename, AbducibleHandler& handler) {
    size_t size = getAbducibleCount(filename);
    handler.allocate(abducibles_memory_id, size);
    std::map<int, int> linker;
    AbducibleParser parser(filename);
    parser.init();
    for (uint32_t i = 0; i < size; i++) {
        if (!parser.isOk()) {
            throw ParseError("Error loading from @file:" + filename);
        }
        handler.handleAbducible(parser.nextAbducible());
    }
}
