#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

#include <map>
#include <list>
#include <starray/starray.hpp>
#include <snlog/snlog.hpp>

namespace gpid {

    template<class SolverT>
    class HypothesesSet {
        typedef uint32_t hyp_index_t ;
        typedef uint32_t level_t ;
        std::map<hyp_index_t, typename SolverT::HypothesisT*> hp_mapping;
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
        inline void mapHypothesis(uint32_t idx, typename SolverT::HypothesisT* hyp);
        inline void mapLink(uint32_t idx, uint32_t tgt_idx);
        inline uint32_t getSize();
        inline uint32_t getSourceSize();
        inline bool isEmpty(uint32_t level);
        inline void skipModelSkippables(level_t level);
        inline typename SolverT::HypothesisT& nextHypothesis(uint32_t level);
        inline void modelCleanUp(typename SolverT::ModelT& model, uint32_t level);
    };

    template<class SolverT>
    inline void HypothesesSet<SolverT>::keepLevel() {
        for (hyp_index_t i : consequences_map[current_level])
            hp_active.activate(i);
        consequences_map[current_level].clear();
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::increaseLevel(uint32_t target) {
        while (current_level < target) {
            ++current_level;
            hp_active.reset_iterator();
            deactivation_map[current_level].clear();
            consequences_map[current_level].clear();
            reactivation_map[current_level].clear();
            modelquences_map[current_level].clear();
        }
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::decreaseLevel(uint32_t target) {
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

    template<class SolverT>
    inline void HypothesesSet<SolverT>::accessLevel(uint32_t level) {
        if (level == current_level) keepLevel();
        else if (level > current_level) increaseLevel(level);
        else decreaseLevel(level);
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::skipModelSkippables(level_t level) {
        accessLevel(level);
        int index = hp_active.get_last();
        while(modelquences_map[current_level][index]) {
            hp_active.deactivate(index);
            deactivation_map[current_level].push_back(index);
            index = hp_active.get_last();
        }
    }

    template<class SolverT>
    inline uint32_t HypothesesSet<SolverT>::getSize() {
        return hp_active.get_activated_size();
    }
    template<class SolverT>
    inline uint32_t HypothesesSet<SolverT>::getSourceSize() {
        return hp_active.get_maximal_size();
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::mapHypothesis(uint32_t idx, typename SolverT::HypothesisT* hyp) {
        hp_mapping[idx] = hyp;
    }
    template<class SolverT>
    inline void HypothesesSet<SolverT>::mapLink(uint32_t idx, uint32_t tgt_idx) {
        hp_links[idx].push_back(tgt_idx);
    }

    template<class SolverT>
    inline bool HypothesesSet<SolverT>::isEmpty(uint32_t level) {
        if (level != current_level) accessLevel(level);
        return hp_active.get_activated_size() == 0;
    }

    template<class SolverT>
    inline typename SolverT::HypothesisT& HypothesesSet<SolverT>::nextHypothesis(uint32_t level) {
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

    template<class SolverT>
    inline void HypothesesSet<SolverT>::modelCleanUp(typename SolverT::ModelT& model, uint32_t level) {
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
