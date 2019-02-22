#define LIB_LISP_TREE_NODE_STRINGIFYER__CPP

#include <snlog/snlog.hpp>
#include <lisptp/lisptp.hpp>

using namespace lisptp;
using LispTreeNodePtr = std::shared_ptr<LispTreeNode>;

static inline const std::string pad(size_t padding) {
    std::string res = "";
    for (size_t p = 0; p < padding; ++p)
        res += ' ';
    return res;
}

void LispTreeNode::str(std::stringstream& ss, size_t padding, bool& padpars, bool pretty) const {
    padpars = true;
    if (isCall()) {
        ss << (pretty ? pad(padding) : "") << '(' << value;
        for (LispTreeNodePtr leaf : leaves) {
            ss << (pretty ? '\n' : ' ');
            leaf->str(ss, padding+1, padpars, pretty);
        }
        if (pretty && padpars) ss << pad(padding);
        ss << ')';
        padpars = false;
    } else {
        ss << (pretty ? pad(padding) : "") << value << (pretty ? "\n" : "");
    }
}

const std::string LispTreeNode::str(bool pretty) const {
    std::stringstream ss;
    bool padpars = false;
    str(ss, 0, padpars, pretty);
    if (pretty) ss << '\n';
    return ss.str();
}
