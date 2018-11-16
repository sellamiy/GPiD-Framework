#define LIB_STARRAY__GLOBAL_ARRAY_BLOC_CPP

#include <map>
#include <starray/GlobalArrayBloc.hpp>

namespace starray {
    class GlobalArrayBloc {
    private:
        void* activePointer;
        std::map<std::string, void*> dataMap;
        std::map<std::string, uint32_t> countMap;
        std::map<std::string, size_t> sizeMap;
    public:
        GlobalArrayBloc();
        ~GlobalArrayBloc();
        inline bool hasTag(const std::string& tag) const;
        inline GAB_Status allocate(const std::string& tag, size_t size);
        inline GAB_Status freeTag(const std::string& tag);
        inline GAB_Status setElmCount(const std::string& tag, uint32_t elm_count);
        inline GAB_Status setElmSize(const std::string& tag, size_t elm_size);
        inline GAB_Status access(const std::string& tag, uint32_t pos);
        inline void* recoverActivePointer() const;
    };
    static GlobalArrayBloc globalArrayBloc;
};

using namespace starray;

GlobalArrayBloc::GlobalArrayBloc() : activePointer(NULL) {}
GlobalArrayBloc::~GlobalArrayBloc() { for (std::pair<std::string, void*> p : dataMap) free(p.second); }

inline bool GlobalArrayBloc::hasTag(const std::string& tag) const {
    return dataMap.find(tag) != dataMap.end();
}

inline void* GlobalArrayBloc::recoverActivePointer() const { return activePointer; }

inline GAB_Status GlobalArrayBloc::allocate(const std::string& tag, size_t size) {
    void* data = malloc(size);
    if (data == NULL) return GAB_Status::ALLOCATION_FAILURE;
    dataMap[tag] = data;
    return GAB_Status::SUCCESS;
}
inline GAB_Status GlobalArrayBloc::setElmCount(const std::string& tag, uint32_t elm_count) {
    if (dataMap[tag] == NULL) return GAB_Status::UNALLOCATED_CONF_STORAGE;
    countMap[tag] = elm_count;
    return GAB_Status::SUCCESS;
}
inline GAB_Status GlobalArrayBloc::setElmSize(const std::string& tag, size_t elm_size) {
    if (dataMap[tag] == NULL) return GAB_Status::UNALLOCATED_CONF_STORAGE;
    sizeMap[tag] = elm_size;
    return GAB_Status::SUCCESS;
}
inline GAB_Status GlobalArrayBloc::access(const std::string& tag, uint32_t pos) {
    if (dataMap[tag] == NULL) return GAB_Status::TAG_UNALLOCATED;
    if (countMap[tag] == 0 || sizeMap[tag] == 0) return GAB_Status::UNCONFED_ACCESS;
    if (countMap[tag] <= pos) return GAB_Status::OOB_ACCESS;
    activePointer = &(((char*)dataMap[tag])[pos*sizeMap[tag]]);
    return GAB_Status::SUCCESS;
}
inline GAB_Status GlobalArrayBloc::freeTag(const std::string& tag) {
    if (dataMap[tag] == NULL) return GAB_Status::TAG_UNALLOCATED;
    free(dataMap[tag]);
    size_t rmc;
    rmc = dataMap.erase(tag);
    rmc += countMap.erase(tag);
    rmc += sizeMap.erase(tag);
    if (rmc != 3) return GAB_Status::TRACKER_CORRUPTION;
    return GAB_Status::SUCCESS;
}

extern GAB_Status starray::requestContinuousArray(const std::string& tag, uint32_t elm_count, size_t elm_size) {
    GAB_Status ret;
    if (globalArrayBloc.hasTag(tag)) return GAB_Status::TAG_DUPLICATION;
    ret = globalArrayBloc.allocate(tag, elm_count*elm_size);
    if (ret != GAB_Status::SUCCESS) return ret;
    ret = globalArrayBloc.setElmCount(tag, elm_count);
    if (ret != GAB_Status::SUCCESS) return ret;
    ret = globalArrayBloc.setElmSize(tag, elm_size);
    return ret;
}

extern GAB_Status starray::releaseContinuousArray(const std::string& tag) {
    GAB_Status ret;
    if (!globalArrayBloc.hasTag(tag)) return GAB_Status::TAG_UNKNOWN;
    ret = globalArrayBloc.freeTag(tag);
    return ret;
}

extern GAB_Status starray::accessContinuousPointer(const std::string& tag, uint32_t elm_pos, void** ptr) {
    GAB_Status ret;
    if (!globalArrayBloc.hasTag(tag)) return GAB_Status::TAG_UNKNOWN;
    ret  = globalArrayBloc.access(tag, elm_pos);
    *ptr = globalArrayBloc.recoverActivePointer();
    return ret;
}
