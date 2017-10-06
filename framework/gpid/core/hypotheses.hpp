#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

#include <map>
#include <list>
#include <starray/starray.hpp>
#include <snlog/snlog.hpp>

namespace gpid {

    template<class HypothesisT, class ModelT>
    class HypothesesSet {
        typedef uint32_t hyp_index_t ;
        typedef uint32_t level_t ;
        std::map<hyp_index_t, HypothesisT*> hp_mapping;
        std::map<hyp_index_t, std::list<hyp_index_t> > hp_links;
        std::map<level_t, std::list<hyp_index_t> > deactivation_map;
        std::map<level_t, std::list<hyp_index_t> > consequences_map;
        std::map<level_t, std::list<hyp_index_t> > reactivation_map;
        std::map<level_t, std::map<hyp_index_t, bool> > modelquences_map;
        starray::StaticActivableArray hp_active;
        level_t current_level;

        inline void keepLevel();
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
        inline void skipModelSkippables(level_t level);
        inline HypothesisT& nextHypothesis(uint32_t level);
        inline void modelCleanUp(ModelT& model, uint32_t level);
    };

    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::keepLevel() {
        for (hyp_index_t i : consequences_map[current_level])
            hp_active.activate(i);
        consequences_map[current_level].clear();
    }

    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::increaseLevel(uint32_t target) {
        while (current_level < target) {
            ++current_level;
            hp_active.reset_iterator();
            deactivation_map[current_level].clear();
            consequences_map[current_level].clear();
            reactivation_map[current_level].clear();
            modelquences_map[current_level].clear();
        }
    }

    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::decreaseLevel(uint32_t target) {
        while (current_level > target) {
            for (hyp_index_t i : reactivation_map[current_level])
                hp_active.deactivate(i);
            for (hyp_index_t i : deactivation_map[current_level])
                hp_active.activate(i);
            for (hyp_index_t i : consequences_map[current_level])
                hp_active.activate(i);
            --current_level;
        }
        keepLevel();
    }

    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::accessLevel(uint32_t level) {
        if (level == current_level) keepLevel();
        else if (level > current_level) increaseLevel(level);
        else decreaseLevel(level);
    }

    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::skipModelSkippables(level_t level) {
        accessLevel(level);
        int index = hp_active.get_last();
        while(modelquences_map[current_level][index]) {
            hp_active.deactivate(index);
            deactivation_map[current_level].push_back(index);
            index = hp_active.get_last();
        }
    }

    template<class HypothesisT, class ModelT>
    inline uint32_t HypothesesSet<HypothesisT, ModelT>::getSize() {
        return hp_active.get_activated_size();
    }
    template<class HypothesisT, class ModelT>
    inline uint32_t HypothesesSet<HypothesisT, ModelT>::getSourceSize() {
        return hp_active.get_maximal_size();
    }

    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::mapHypothesis(uint32_t idx, HypothesisT* hyp) {
        hp_mapping[idx] = hyp;
    }
    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::mapLink(uint32_t idx, uint32_t tgt_idx) {
        hp_links[idx].push_back(tgt_idx);
    }

    template<class HypothesisT, class ModelT>
    inline bool HypothesesSet<HypothesisT, ModelT>::isEmpty(uint32_t level) {
        if (level != current_level) accessLevel(level);
        return hp_active.get_activated_size() == 0;
    }

    template<class HypothesisT, class ModelT>
    inline HypothesisT& HypothesesSet<HypothesisT, ModelT>::nextHypothesis(uint32_t level) {
        // accessLevel(level);
        int index = hp_active.get_last();
        hp_active.deactivate(index);
        deactivation_map[current_level].push_back(index);
        for (int linked_index : hp_links[index]) {
            if (hp_active.is_active(linked_index)) {
                hp_active.deactivate(linked_index);
                consequences_map[current_level].push_back(linked_index);
            }
        }
        return *hp_mapping[index];
    }

    template<class HypothesisT, class ModelT>
    inline void HypothesesSet<HypothesisT, ModelT>::modelCleanUp(ModelT& model, uint32_t level) {
        if (isEmpty(level)) return;
        hp_active.reset_iterator();
        while (hp_active.has_next()) {
            uint32_t l_idx = hp_active.get_next();
            if (model.isSkippable(*hp_mapping[l_idx])) {
                modelquences_map[current_level][l_idx] = true;
            }
        }
    }

};

#endif
