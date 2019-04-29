#define LIB_WHY3CPP__PLATFORM_GENERAL_UTILS_CPP

#include <stdutils/strings.hpp>
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

static inline const std::string floatize(const std::string& s) {
    return (s == "=" || s == "<>") ? s : s + ".";
}

static inline bool detected_float(const std::string& data) {
    return data.find("from_int") != std::string::npos
        || data.find(".") != std::string::npos;
    // TODO: Add correct handle for variables
}

std::string Why3Smtl2CV::handle_call(const std::string& op, const std::vector<std::string>& lvs) const {
    const std::string& ops = cmap.hasForwardMapping(op) ? cmap.forwardMapping(op) : op;
    if (ops == "and" || ops == "AND")
        return parenthize(stdutils::join(" /\\ ", lvs));
    if (ops == "or" || ops == "OR")
        return parenthize(stdutils::join(" \\/ ", lvs));
    if (ops == "distinct" || ops == "DISTINCT")
        return parenthize(stdutils::join(" <> ", lvs));
    if (ops == "not" || ops == "NOT")
        return parenthize("not " + stdutils::join("", lvs));
    if (is_prefix(ops))
        return parenthize(ops + " " + lvs.front());
    if (is_infix(ops)) {
        for (const std::string& p : lvs)
            if (detected_float(p))
                return parenthize(stdutils::join(space(floatize(ops)), lvs));
        return parenthize(stdutils::join(space(ops), lvs));
    }
    return parenthize(ops + " " + stdutils::join(" ", lvs));
}

std::string BackwardSmtl2CV::handle_call(const std::string& op, const std::vector<std::string>& lvs) const {
    const std::string& ops = cmap.hasBackwardMapping(op) ? cmap.backwardMapping(op) : op;
    return parenthize(ops + " " + stdutils::join(" ", lvs));
}
