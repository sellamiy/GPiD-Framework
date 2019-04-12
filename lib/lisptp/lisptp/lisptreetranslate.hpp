#ifndef LIB_LISP_TREE_PARSER__LISP_TREE_TRANSLATE_HEADER
#define LIB_LISP_TREE_PARSER__LISP_TREE_TRANSLATE_HEADER

#include <map>
#include <lisptp/lisptree.hpp>

namespace lisptp {

    using translation_map_t = std::map<std::string, std::string>;

    class LispTreeTranslator {
        const translation_map_t& tmap;
    public:
        LispTreeTranslator(const translation_map_t& tmap) : tmap(tmap) {}
        inline LispTreeNodePtr translate(LispTreeNodePtr node) const;
    };

    inline LispTreeNodePtr LispTreeTranslator::translate(LispTreeNodePtr node) const {
        if (node->isCall()) {
            std::vector<LispTreeNodePtr> lvs;
            for (auto leaf : node->getLeaves())
                lvs.push_back(translate(leaf));
            if (tmap.count(node->getValue()) > 0)
                return alloc_ltn_ptr(tmap.at(node->getValue()), true, lvs);
            else
                return alloc_ltn_ptr(node->getValue(), true, lvs);
        } else {
            if (tmap.count(node->getValue()) > 0)
                return alloc_ltn_ptr(tmap.at(node->getValue()), false, node->getLeaves());
            else
                return node;
        }
    }

}

#endif
