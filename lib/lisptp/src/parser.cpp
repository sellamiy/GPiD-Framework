#define LIB_LISP_TREE_PARSER__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <lisptp/lisptp.hpp>

using namespace lisptp;
using LispTreeNodePtr = std::shared_ptr<LispTreeNode>;

static inline constexpr bool isWSC(char c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t' ;
}

static inline constexpr bool isOpar(char c) { return c == '('; }
static inline constexpr bool isCpar(char c) { return c == ')'; }
static inline constexpr bool isPar(char c) { return isOpar(c) || isCpar(c); }

/*
static inline void nextWSC(const std::string& data, size_t& pos) {
    while (pos < data.length() && !isWSC(data.at(pos))) ++pos;
}
*/

static inline void nextHookC(const std::string& data, size_t& pos) {
    while (pos < data.length() && !isWSC(data.at(pos)) && !isPar(data.at(pos))) ++pos;
}

static inline void nextNonWSC(const std::string& data, size_t& pos) {
    while (pos < data.length() && isWSC(data.at(pos))) ++pos;
}

static LispTreeNodePtr parse_lisp_text(const std::string& data, size_t& pos) {
    nextNonWSC(data, pos);
    if (pos >= data.length() || isCpar(data.at(pos))) {
        // TODO: Error
    }
    std::string value;
    bool callstate;
    std::list<LispTreeNodePtr> leaves;
    if (isOpar(data.at(pos))) {
        callstate = true;
        ++pos;
        nextNonWSC(data, pos);
        size_t loc = pos;
        nextHookC(data, pos);
        value = data.substr(loc, pos-loc);
        nextNonWSC(data, pos); // TODO : Possible error case Here
        while (!isCpar(data.at(pos))) {
            leaves.push_back(parse_lisp_text(data, pos));
            nextNonWSC(data, pos);
        }
        ++pos;
    } else {
        callstate = false;
        size_t loc = pos;
        nextHookC(data, pos);
        value = data.substr(loc, pos-loc);
    }
    return LispTreeNodePtr(new LispTreeNode(value, callstate, leaves));
}

extern LispTreeNodePtr lisptp::parse(const std::string& data) {
    size_t pos = 0;
    LispTreeNodePtr global = parse_lisp_text("(_glb_ " + data + ")", pos);
    if (global->getLeaves().size() == 1)
        return global->getLeaves().front();
    return LispTreeNodePtr(new LispTreeNode("", true, global->getLeaves()));
}

extern LispTreeNodePtr lisptp::parse_file(const std::string& fname) {
    std::stringstream ss;
    std::ifstream data(fname);
    if (data.is_open()) {
        ss << data.rdbuf();
        data.close();
    }
    return parse(ss.str());
}
