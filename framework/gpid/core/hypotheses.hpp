#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

#include <map>
#include <list>
#include <starray/starray.hpp>
#include <snlog/snlog.hpp>

namespace gpid {

    template<class HypothesisT>
    class HypothesesSet {
        typedef uint32_t hyp_index_t ;
        typedef uint32_t level_t ;
        std::map<hyp_index_t, HypothesisT*> hp_mapping;
        std::map<hyp_index_t, std::list<hyp_index_t> > hp_links;
        std::map<level_t, std::list<hyp_index_t> > deactivation_map;
        std::map<level_t, std::list<hyp_index_t> > reactivation_map;
        starray::StaticActivableArray hp_active;
        level_t current_level;

        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);
    public:
        HypothesesSet(uint32_t size) : hp_active(size), current_level(0) {}
        inline void mapHypothesis(uint32_t idx, HypothesisT* hyp);
        inline void mapLink(uint32_t idx, uint32_t tgt_idx);
        inline uint32_t getSize();
        inline uint32_t getSourceSize();
        inline bool isEmpty(uint32_t level);
        inline HypothesisT& nextHypothesis(uint32_t level);
    };

    template<class HypothesisT>
    inline void HypothesesSet<HypothesisT>::increaseLevel(uint32_t target) {
        while (current_level < target) {
            ++current_level;
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
        }
    }

    template<class HypothesisT>
    inline void HypothesesSet<HypothesisT>::accessLevel(uint32_t level) {
        if (level > current_level) increaseLevel(level);
        else decreaseLevel(level);
    }

    template<class HypothesisT>
    inline uint32_t HypothesesSet<HypothesisT>::getSize() {
        return hp_active.get_activated_size();
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
    inline void HypothesesSet<HypothesisT>::mapLink(uint32_t idx, uint32_t tgt_idx) {
        hp_links[idx].push_back(tgt_idx);
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
        accessLevel(level);
        hp_active.reset_iterator();
        int index = hp_active.get_next();
        hp_active.deactivate(index);
        deactivation_map[current_level].push_back(index);
        for (int linked_index : hp_links[index]) {
            hp_active.deactivate(linked_index);
            deactivation_map[current_level].push_back(linked_index);
        }
        return *hp_mapping[index];
    }

};

#endif
