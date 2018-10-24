#ifndef LIB_SMTLIB2_UTILS__SMTLIB2_STRING_MEMORY_HPP
#define LIB_SMTLIB2_UTILS__SMTLIB2_STRING_MEMORY_HPP

#include <string>
#include <sstream>
#include <memory>

namespace smtlib2utils {

    class SMTl2StringMemoryData;

    class SMTl2StringMemory {
        std::unique_ptr<SMTl2StringMemoryData> data;
    public:
        SMTl2StringMemory();
        ~SMTl2StringMemory();

        std::shared_ptr<std::string> alloc(const std::string& s);
        std::shared_ptr<std::string> alloc(const std::stringstream& s);
    };

}

#endif
