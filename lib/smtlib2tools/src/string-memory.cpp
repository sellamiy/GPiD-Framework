#define LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_STRING_MEMORY_CPP

#include <vector>
#include <snlog/snlog.hpp>
#include <smtlib2tools/string-memory.hpp>

namespace smtlib2 {

    class StringMemoryData {
    public:
        std::vector<std::shared_ptr<smtident_t>> plist;
    };

    StringMemory::StringMemory() : data(new StringMemoryData()) {}
    StringMemory::~StringMemory() {}

    std::shared_ptr<smtident_t> StringMemory::alloc(const smtident_t& s) {
        data->plist.push_back(std::shared_ptr<smtident_t>(new smtident_t(s)));
        return data->plist.back();
    }

    std::shared_ptr<smtident_t> StringMemory::alloc(const std::stringstream& s) {
        data->plist.push_back(std::shared_ptr<smtident_t>(new smtident_t(s.str())));
        return data->plist.back();
    }

}
