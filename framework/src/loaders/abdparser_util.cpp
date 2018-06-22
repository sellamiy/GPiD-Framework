#define GPID_FRAMEWORK__UTIL__ABDPARSER_UTIL_CPP

#include <snlog/snlog.hpp>
#include <gpid/core/errors.hpp>
#include <gpid/loaders/abdparser.hpp>

using namespace snlog;
using namespace gpid;

extern uint32_t gpid::getAbducibleCount(std::string filename) {
    AbducibleParser parser(filename);
    parser.init();
    if (parser.isOk()) {
        return parser.getAbducibleCount();
    } else {
        throw ParseError("Failed to count abducibles in @file:" + filename);
    }
}