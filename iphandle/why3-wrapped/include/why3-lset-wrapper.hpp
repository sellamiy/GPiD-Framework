#ifndef WHY3_WHYML_IPH_FOR_GPID__LSET__HPP
#define WHY3_WHYML_IPH_FOR_GPID__LSET__HPP

#include <why3cpp/why3proof.hpp>
#include <why3cpp/why3utils.hpp>

class Why3_LSet {
    std::vector<std::string> literals;
    std::set<std::string> references;
public:
    Why3_LSet
    (const std::string& filename, const why3cpp::Why3ConvertMap& cmap, bool overriden, bool shuffle);
    inline const std::vector<std::string>& getLiterals() const { return literals; }
    inline const std::set<std::string>& getReferences() const { return references; }
};

#endif
