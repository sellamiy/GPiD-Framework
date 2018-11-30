#define LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_CPP

#include <why3cpp/why3utils.hpp>

using namespace why3cpp;

static inline std::string space(const std::string s) { return " " + s + " "; }

static inline std::string parenthize(const std::string s) { return "(" + s + ")"; }

static inline std::string join(const std::string& jer, const std::list<std::string>& elems) {
    if (elems.size() == 0) return "";
    if (elems.size() == 1) return elems.front();
    std::stringstream res;
    bool start = true;
    for (auto elem : elems) {
        if (start) {
            res << elem;
            start = false;
        } else {
            res << jer << elem;
        }
    }
    return res.str();
}

std::string Why3Smtl2CV::handle_call(const std::string& op, const std::list<std::string>& lvs) const {
    if (op == "and" || op == "AND")
        return parenthize(join(" /\\ ", lvs));
    if (op == "or" || op == "OR")
        return parenthize(join(" \\/ ", lvs));
    if (op == "distinct" || op == "DISTINCT")
        return parenthize(join(" <> ", lvs));
    if (op == "not" || op == "NOT")
        return parenthize("not " + join("", lvs));
    if (lvs.size() == 2)
        return parenthize(join(space(op), lvs));
    return "(#ERROR#)";
}
