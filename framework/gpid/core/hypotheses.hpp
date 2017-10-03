#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

#include <map>
#include <list>
#include <starray/starray.hpp>

namespace gpid {

    template<class HypothesisT>
    class HypothesesSet {
        typedef uint32_t hyp_index_t ;
        typedef uint32_t level_t ;
        std::map<hyp_index_t, HypothesisT*> hp_mapping;
        std::map<level_t, hyp_index_t> index_table;
        std::map<level_t, std::list<hyp_index_t> > deactivation_map;
        std::map<level_t, std::list<hyp_index_t> > reactivation_map;
        starray::StaticActivableArray hp_active;
        level_t current_level;

        inline hyp_index_t getIndex() { return index_table[current_level]; }
        inline void setIndex(hyp_index_t id) { index_table[current_level] = id; }
        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);
    public:
        HypothesesSet(uint32_t size) : hp_active(size), current_level(0) {}
        inline void mapHypothesis(uint32_t idx, HypothesisT* hyp);
        inline uint32_t getSourceSize();
        inline bool isEmpty(uint32_t level);
        inline HypothesisT& nextHypothesis(uint32_t level);
    };

    template<class HypothesisT>
    inline void HypothesesSet<HypothesisT>::increaseLevel(uint32_t target) {
        while (current_level < target) {
            ++current_level;
            setIndex(hp_active.get_first());
            hp_active.reset_iterator();
            deactivation_map[current_level].clear();
            reactivation_map[current_level].clear();
        }
    }

    template<class HypothesisT>
    inline void HypothesesSet<HypothesisT>::decreaseLevel(uint32_t target) {
        while (current_level > target) {
            for (hyp_index_t i : reactivation_map[current_level])
                hp_active.deactivate(i);
            for (hyp_index_t i : deactivation_map[current_level])
                hp_active.activate(i);
            --current_level;
            hp_active.set_it_pos(getIndex());
        }
    }

    template<class HypothesisT>
    inline void HypothesesSet<HypothesisT>::accessLevel(uint32_t level) {
        if (level > current_level) increaseLevel(level);
        else decreaseLevel(level);
    }

    template<class HypothesisT>
    inline uint32_t HypothesesSet<HypothesisT>::getSourceSize() {
        return hp_active.get_maximal_size();
    }

    template<class HypothesisT>
    inline void HypothesesSet<HypothesisT>::mapHypothesis(uint32_t idx, HypothesisT* hyp) {
        hp_mapping[idx] = hyp;
    }

    template<class HypothesisT>
    inline bool HypothesesSet<HypothesisT>::isEmpty(uint32_t level) {
        if (level != current_level) {
            accessLevel(level);
        }
        return hp_active.get_activated_size() == 0;
    }

    template<class HypothesisT>
    inline HypothesisT& HypothesesSet<HypothesisT>::nextHypothesis(uint32_t level) {
        bool need_skip = level <= current_level;
        accessLevel(level);
        if (need_skip) {
            hyp_index_t todeac = getIndex();
            setIndex(hp_active.get_next());
            hp_active.deactivate(todeac);
            deactivation_map[current_level].push_back(todeac);
        }
        return *hp_mapping[getIndex()];
    }

};

#endif
