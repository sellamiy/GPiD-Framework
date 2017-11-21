#define GPID_FRAMEWORK__UTIL__ABDPARSER_UTIL_CPP

#include <snlog/snlog.hpp>
#include <gpid/util/parsers.hpp>

using namespace snlog;
using namespace gpid;

extern uint32_t gpid::getAbducibleCount(std::string filename) {
    AbducibleParser parser(filename);
    parser.init();
    if (parser.isOk()) {
        return parser.getAbducibleCount();
    } else {
        l_fatal("Failed to count abducibles in @file:" + filename);
        return 0;
    }
}
