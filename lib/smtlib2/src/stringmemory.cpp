#define LIB_SMTLIB2_UTILS__SMTLIB2_STRING_MEMORY_CPP

#include <vector>
#include <snlog/snlog.hpp>
#include <smtlib2utils/StringMemory.hpp>

namespace smtlib2utils {

    class SMTl2StringMemoryData {
    public:
        std::vector<std::shared_ptr<std::string>> plist;
    };

    SMTl2StringMemory::SMTl2StringMemory() : data(new SMTl2StringMemoryData()) {}
    SMTl2StringMemory::~SMTl2StringMemory() {}

    std::shared_ptr<std::string> SMTl2StringMemory::alloc(const std::string& s) {
        data->plist.push_back(std::shared_ptr<std::string>(new std::string(s)));
        return data->plist.back();
    }

    std::shared_ptr<std::string> SMTl2StringMemory::alloc(const std::stringstream& s) {
        data->plist.push_back(std::shared_ptr<std::string>(new std::string(s.str())));
        return data->plist.back();
    }

}
