#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

#include <map>
#include <Memory.hpp>

namespace gpid {

    template<class HypothesisT>
    class HypothesesSet {
        std::map<uint32_t, HypothesisT*> hp_mapping;
        uint32_t valid_access_level;
        // memory::lv_tab<uint32_t> access_table;
    public:
        bool isEmpty(uint32_t level);
        HypothesisT& nextHypothesis(uint32_t level);
    };

    template<class HypothesisT>
    inline bool HypothesesSet<HypothesisT>::isEmpty(uint32_t level) {
        // return access_table.has_next(level);
    }

    template<class HypothesisT>
    inline HypothesisT& HypothesesSet<HypothesisT>::nextHypothesis(uint32_t level) {
        /*
        if (level > valid_access_level) {
            access_table.extend(level);
        } else {
            access_table.shrink(level);
            access_table.unset_current(level);
            access_table.skip_current(level);
        }
        access_table.set_current(level);
        return *hp_mapping[access_table.get_current(level)];
        */
    }

};

#endif
