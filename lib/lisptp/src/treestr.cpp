#define LIB_LISP_TREE_NODE_STRINGIFYER__CPP

#include <snlog/snlog.hpp>
#include <lisptp/lisptp.hpp>

using namespace lisptp;
using LispTreeNodePtr = std::shared_ptr<LispTreeNode>;

void LispTreeNode::str(std::stringstream& ss) const {
    if (isCall()) {
        ss << "(" << value;
        for (LispTreeNodePtr leaf : leaves) {
            ss << " ";
            leaf->str(ss);
        }
        ss << ")";
    } else {
        ss << value;
    }
}

const std::string LispTreeNode::str() const {
    std::stringstream ss;
    str(ss);
    return ss.str();
}
