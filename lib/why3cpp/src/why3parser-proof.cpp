#define LIB_WHY3CPP__PARSERS_PROOF_CPP

#include <sstream>
#include <snlog/snlog.hpp>
#include <why3cpp/why3proofutils.hpp>

namespace why3cpp {

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

}

using namespace why3cpp;

void SplitProofParser::parse() {
    std::istringstream stream = std::istringstream(*data);
    std::string line;
    uint32_t index = 0;
    while (getline(stream, line))
        if (is_anchor(line, anchor))
            proof.push_back(SplitProofResult(index++, extract_status(line)));
}
