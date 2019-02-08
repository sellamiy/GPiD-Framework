#define LIB_WHY3CPP__PARSERS_VC_CPP

#include <sstream>
#include <snlog/snlog.hpp>
#include <why3cpp/why3proofutils.hpp>

namespace why3cpp {

    static inline bool is_anchor(const std::string& line) {
        return line.find(";; produced by") == 0
            || line == ";;; this is a prelude for Alt-Ergo";
        // TODO: This is conseq of Why3 drivers; Move this to a template generated from wtf....py
    }

}

using namespace why3cpp;

void SplitProofVCParser::parse() {
    std::istringstream stream = std::istringstream(*data);
    std::stringstream partial;
    std::string line;
    bool start = true;
    uint32_t index = 0;
    while (getline(stream, line)) {
        if (is_anchor(line)) {
            if (start) start = false;
            else vcs[index++] = strptr(new std::string(partial.str()));
            partial.str(std::string());
        } else {
            partial << line << '\n';
        }
    }
    vcs[index++] = strptr(new std::string(partial.str())); // Last vc
}
