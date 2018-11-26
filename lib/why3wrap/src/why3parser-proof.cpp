#define LIB_WHY3WRAP__PARSERS_PROOF_CPP

#include <sstream>
#include <snlog/snlog.hpp>
#include <why3wrap/why3proofutils.hpp>

namespace why3wrap {

    static inline bool is_anchor(const std::string& line, const std::string& anchor) {
        return line.find(anchor) == 0;
    }

    static inline ProofElemStatus extract_status(const std::string& line) {
        size_t ppos = line.find(":");
        if (line.find("Valid", ppos) != std::string::npos)
            return ProofElemStatus::Valid;
        if (line.find("Invalid", ppos) != std::string::npos)
            return ProofElemStatus::Invalid;
        if (line.find("Unknown", ppos) != std::string::npos)
            return ProofElemStatus::Unknown;
        // TODO : Signal Internal Error here
        return ProofElemStatus::Unknown;
    }

    static inline void update_explanation(const std::string& line, std::string& expl) {
        size_t ipos = line.find("[@expl");
        if (ipos != std::string::npos) {
            size_t kpos = line.find("]", ipos);
            expl = line.substr(ipos + 2, kpos - ipos - 2);
        }
    }

}

using namespace why3wrap;

void SplitProofParser::parse() {
    std::istringstream stream = std::istringstream(*data);
    std::string line;
    std::string expl;
    uint32_t index = 0;
    while (getline(stream, line))
        if (is_anchor(line, anchor))
            proof.push_back(SplitProofResult(index++, expl, extract_status(line)));
        else
            update_explanation(line, expl);
}
