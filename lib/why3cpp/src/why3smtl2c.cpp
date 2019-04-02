#define LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_CPP

#include <why3cpp/why3utils.hpp>

using namespace why3cpp;

static inline std::string space(const std::string s) { return " " + s + " "; }

static inline std::string parenthize(const std::string s) { return "(" + s + ")"; }

static inline bool is_infix(const std::string& s) {
    return s == "+"
        || s == "-"
        || s == "/"
        || s == "*"
        || s == ">"
        || s == "<"
        || s == ">="
        || s == "<="
        || s == "="
        ;
}

static inline bool is_prefix(const std::string& s) {
    return s == "-";
}

static inline std::string join(const std::string& jer, const std::vector<std::string>& elems) {
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

std::string Why3Smtl2CV::handle_call(const std::string& op, const std::vector<std::string>& lvs) const {
    const std::string& ops = cmap.hasForwardMapping(op) ? cmap.forwardMapping(op) : op;
    if (ops == "and" || ops == "AND")
        return parenthize(join(" /\\ ", lvs));
    if (ops == "or" || ops == "OR")
        return parenthize(join(" \\/ ", lvs));
    if (ops == "distinct" || ops == "DISTINCT")
        return parenthize(join(" <> ", lvs));
    if (ops == "not" || ops == "NOT")
        return parenthize("not " + join("", lvs));
    if (is_prefix(ops))
        return parenthize(ops + " " + lvs.front());
    if (is_infix(ops))
        return parenthize(join(space(ops), lvs));
    return parenthize(ops + " " + join(" ", lvs));
}

std::string BackwardSmtl2CV::handle_call(const std::string& op, const std::vector<std::string>& lvs) const {
    const std::string& ops = cmap.hasBackwardMapping(op) ? cmap.backwardMapping(op) : op;
    return parenthize(ops + " " + join(" ", lvs));
}
