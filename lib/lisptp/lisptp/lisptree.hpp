#ifndef LIB_LISP_TREE_PARSER__LISP_TREE_HEADER
#define LIB_LISP_TREE_PARSER__LISP_TREE_HEADER

#include <string>
#include <sstream>
#include <vector>
#include <memory>

namespace lisptp {

    class LispTreeNode {
    public:
        using LispTreeNodePtr = std::shared_ptr<LispTreeNode>;
    private:
        const std::string value;
        const bool callstate;
        const std::vector<LispTreeNodePtr> leaves;
        void str(std::stringstream& ss, size_t pad, bool& ep, bool pretty) const;
    public:
        LispTreeNode(const std::string v, bool cs, const std::vector<LispTreeNodePtr> ls)
            : value(v), callstate(cs), leaves(ls) {}
        LispTreeNode(const LispTreeNode& o)
            : value(o.value), callstate(o.callstate), leaves(o.leaves) {}

        inline constexpr bool isCall() const { return callstate; }
        inline const std::string& getValue() const { return value; }
        inline const std::vector<LispTreeNodePtr>& getLeaves() const { return leaves; }

        const std::string str(bool pretty=true) const;
    };

}

#endif
