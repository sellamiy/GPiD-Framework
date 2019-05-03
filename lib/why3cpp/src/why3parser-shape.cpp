#define LIB_WHY3CPP__PARSERS_VC_CPP

#include <sstream>
#include <snlog/snlog.hpp>
#include <why3cpp/why3shape.hpp>

namespace why3cpp {

    static inline bool is_shape_anchor(const std::string& line) {
        return line.find(WHY3CPP_SHAPE_ANCHOR_DATA) != std::string::npos;
    }

    static inline bool is_definition_expl(const std::string& expl) {
        return expl == "VC for main";
    }

    static inline void update_mode(std::string& mode, const std::string& line) {
        if (line.length() > 0 && line.at(0) != ' ' && line.at(0) != '(') {
            size_t end = 0;
            while (end < line.length() && line.at(end) != ' ') ++end;
            mode = line.substr(0, end);
        }
    }

    static inline void update_expl(std::string& expl, const std::string& mode, const std::string& line) {
        if (mode == "goal") {
            size_t ipos = line.find("[@expl");
            if (ipos != std::string::npos) {
                size_t kpos = line.find("]", ipos);
                const std::string dexpl = line.substr(ipos + 2, kpos - ipos - 2);
                if (!is_definition_expl(dexpl))
                    expl = dexpl;
            }
        }
    }

}

using namespace why3cpp;

extern ProblemShape why3cpp::parse_shape_data(const std::string& shapedata) {
    ProblemShape result;
    size_t index = 0;
    bool start = true;
    std::istringstream stream = std::istringstream(shapedata);
    std::string line;

    std::string mode = "";
    std::string detected_expl = "";

    while (getline(stream, line)) {
        if (is_shape_anchor(line)) {
            if (start) start = false;
            else result.emplace(index++, detected_expl);
            mode = "";
            detected_expl = "";
        } else {
            update_mode(mode, line);
            update_expl(detected_expl, mode, line);
        }
    }
    result.emplace(index++, detected_expl); // Last vc

    return result;
}
