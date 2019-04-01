#ifndef LIB_WHY3CPP__PLATFORM_PROOF_UTILS_HEADER
#define LIB_WHY3CPP__PLATFORM_PROOF_UTILS_HEADER

#include <map>
#include <vector>
#include <memory>
#include <why3cpp/why3config.hpp>

namespace why3cpp {

    using strptr = std::shared_ptr<std::string>;

    enum class ProofElemStatus { Valid, Invalid, Unknown };
    struct SplitProofResult {
        const uint32_t index;
        const std::string expl;
        const ProofElemStatus status;
        SplitProofResult(uint32_t index, const std::string expl, ProofElemStatus status)
            : index(index), expl(expl), status(status) {}
        inline constexpr bool isValid() const
        { return status == ProofElemStatus::Valid; }
        inline constexpr bool isInvalid() const
        { return status == ProofElemStatus::Invalid; }
        inline constexpr bool isUnknown() const
        { return status == ProofElemStatus::Unknown; }
    };

    class SplitProofParser {
        const std::string anchor;
        strptr data;
        const bool valid;
        std::vector<SplitProofResult> proof;
    public:
        SplitProofParser(const std::string& anchor, strptr data)
            : anchor(anchor), data(data), valid(*data != "") {}
        void parse();
        const std::vector<SplitProofResult>& results() const { return proof; }
        inline constexpr bool isValid() const { return valid; }
    };

    class SplitProofVCParser {
        strptr data;
        std::map<uint32_t, strptr> vcs;
    public:
        SplitProofVCParser(strptr data) : data(data) {}
        void parse();
        const strptr getVC(uint32_t idx) const { return vcs.at(idx); }
    };

    extern strptr vc_sanitization(strptr data, bool reoder=true);

}

#endif
