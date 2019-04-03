#define LIB_LISP_TREE_PARSER__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <lisptp/lisptp.hpp>

using namespace lisptp;
using LispTreeNodePtr = std::shared_ptr<LispTreeNode>;

static inline constexpr bool isWSC(const char& c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t' ;
}

static inline constexpr bool isOpar(const char& c) { return c == '('; }
static inline constexpr bool isCpar(const char& c) { return c == ')'; }
static inline constexpr bool isPar(const char& c) { return isOpar(c) || isCpar(c); }

static inline constexpr bool isCommentStart(const char& c, const char& _hook) {
    return _hook == ' ' && c == ';';
}

static inline constexpr bool isCommentContainer(const char& c, const char& _hook) {
    return _hook == ' ' ? (c == '\'' || c == '"') : c == _hook;
}

/*
  static inline void nextWSC(const std::string& data, size_t& pos) {
  while (pos < data.length() && !isWSC(data.at(pos))) ++pos;
  }
*/

static inline void updateHook(char& _hook, const char& c) {
    isCommentContainer(c, _hook) ? _hook = (_hook == ' ' ? c : ' ') : ' ';
}

static inline void skipComment(const std::string& data, size_t& pos) {
    while (pos < data.length() && data.at(pos) != '\n') ++pos;
}

static inline void nextHookC(const std::string& data, size_t& pos, char& _hook) {
    while (pos < data.length() && !isWSC(data.at(pos)) && !isPar(data.at(pos))) {
        updateHook(_hook, data.at(pos));
        if (isCommentStart(data.at(pos), _hook)) skipComment(data, pos);
        ++pos;
    }
}

static inline void nextNonWSC(const std::string& data, size_t& pos, char& _hook) {
    while (pos < data.length() && isWSC(data.at(pos))) {
        updateHook(_hook, data.at(pos));
        if (isCommentStart(data.at(pos), _hook)) skipComment(data, pos);
        ++pos;
    }
}

static LispTreeNodePtr parse_lisp_text(const std::string& data, size_t& pos, char& _hook) {
    nextNonWSC(data, pos, _hook);
    if (pos >= data.length() || isCpar(data.at(pos))) {
        // TODO: Error
    }
    std::string value;
    bool callstate;
    std::vector<LispTreeNodePtr> leaves;
    if (isOpar(data.at(pos))) {
        callstate = true;
        ++pos;
        nextNonWSC(data, pos, _hook);
        size_t loc = pos;
        nextHookC(data, pos, _hook);
        value = data.substr(loc, pos-loc);
        nextNonWSC(data, pos, _hook); // TODO : Possible error case Here
        while (!isCpar(data.at(pos))) {
            leaves.push_back(parse_lisp_text(data, pos, _hook));
            nextNonWSC(data, pos, _hook);
        }
        ++pos;
    } else {
        callstate = false;
        size_t loc = pos;
        nextHookC(data, pos, _hook);
        value = data.substr(loc, pos-loc);
    }
    return LispTreeNodePtr(new LispTreeNode(value, callstate, leaves));
}

extern LispTreeNodePtr lisptp::parse(const std::string& data) {
    size_t pos = 0;
    char _hook = ' ';
    LispTreeNodePtr global = parse_lisp_text("(" + global_name_wrapper + " " + data + ")", pos, _hook);
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
