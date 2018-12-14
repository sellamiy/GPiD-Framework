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

void LispTreeNode::str(std::stringstream& ss, size_t padding, bool& padpars) const {
    padpars = true;
    if (isCall()) {
        ss << pad(padding) << '(' << value;
        for (LispTreeNodePtr leaf : leaves) {
            ss << '\n';
            leaf->str(ss, padding+1, padpars);
        }
        if (padpars) ss << pad(padding);
        ss << ')';
        padpars = false;
    } else {
        ss << pad(padding) << value << '\n';
    }
}

const std::string LispTreeNode::str() const {
    std::stringstream ss;
    bool padpars = false;
    str(ss, 0, padpars);
    ss << '\n';
    return ss.str();
}
