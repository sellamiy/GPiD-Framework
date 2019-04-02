#ifndef LIB_LISP_TREE_PARSER__LISP_TREE_VISITOR_HEADER
#define LIB_LISP_TREE_PARSER__LISP_TREE_VISITOR_HEADER

#include <lisptp/lisptree.hpp>

namespace lisptp {

    template <typename RT>
    class LispTreeVisitor {
        inline RT _visit(const LispTreeNode& node) const;
    protected:
        virtual RT handle_term(const std::string& t) const = 0;
        virtual RT handle_call(const std::string& op, const std::vector<RT>& lvs) const = 0;
    public:
        inline RT visit(const LispTreeNode& node) const { return _visit(node); }
        inline RT visit(std::shared_ptr<LispTreeNode> node) const { return _visit(*node); }
    };

    template <typename RT>
    inline RT LispTreeVisitor<RT>::_visit(const LispTreeNode& node) const {
        if (node.isCall()) {
            std::vector<RT> lvs;
            for (auto leaf : node.getLeaves())
                lvs.push_back(_visit(*leaf));
            return handle_call(node.getValue(), lvs);
        } else {
            return handle_term(node.getValue());
        }
    }

    template <typename RT>
    class DepthAwareLispTreeVisitor {
        inline RT _visit(const LispTreeNode& node, size_t depth=0) const;
    protected:
        virtual RT handle_term(const std::string& t, size_t depth) const = 0;
        virtual RT handle_call(const std::string& op, const std::vector<RT>& lvs, size_t depth) const = 0;
    public:
        inline RT visit(const LispTreeNode& node) const { return _visit(node); }
        inline RT visit(std::shared_ptr<LispTreeNode> node) const { return _visit(*node); }
    };

    template <typename RT>
    inline RT DepthAwareLispTreeVisitor<RT>::_visit(const LispTreeNode& node, size_t depth) const {
        if (node.isCall()) {
            std::vector<RT> lvs;
            for (auto leaf : node.getLeaves())
                lvs.push_back(_visit(*leaf, depth+1));
            return handle_call(node.getValue(), lvs, depth);
        } else {
            return handle_term(node.getValue(), depth);
        }
    }

}

#endif
