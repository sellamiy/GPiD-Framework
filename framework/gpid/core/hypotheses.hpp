#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

#include <map>
#include <list>
#include <starray/starray.hpp>
#include <snlog/snlog.hpp>
#include <gpid/util/skipper_controller.hpp>

#include <gpid/instrument/instrument.hpp>

namespace gpid {

    template<class SolverT>
    class HypothesisSkipper {
        SolverT& solver;
        SkipperController& actives;
    public:
        HypothesisSkipper(SolverT& s, SkipperController& ctrler)
            : solver(s), actives(ctrler) {}

        inline bool canBeSkipped(typename SolverT::HypothesisT& h, uint32_t level);
    };

    /** Class for handling abducible hypotheses. */
    template<class SolverT>
    class HypothesesSet {
    public:
        typedef typename SolverT::HypothesisT HypothesisT;
        typedef typename SolverT::ModelT ModelT;
    private:
        HypothesisSkipper<SolverT> skipper;

        typedef uint32_t index_t;
        typedef uint32_t level_t;
        starray::SequentialActivableArray      hp_active;
        std::map<index_t, HypothesisT*>        hp_mapping;
        std::map<index_t, std::list<index_t> > hp_links;

        std::map<level_t, std::list<index_t> >  selection_map;
        std::map<level_t, std::list<index_t> > pselection_map;

        std::map<level_t, index_t> limit;
        std::map<level_t, index_t> pointer;
        level_t clevel;

        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);

        inline void unselectLevel(level_t level);

        inline void selectCurrentHypothesis();
    public:
        HypothesesSet(SolverT& solver, SkipperController& ctrler, uint32_t size)
            : skipper(solver, ctrler), hp_active(size), clevel(1)
        { limit[1] = 0; pointer[1] = size; }
        /** Map an index of the set to a specific hypothesis. */
        inline void mapHypothesis(uint32_t idx, HypothesisT* hyp);
        /** Specify incompatible hypotheses. */
        inline void mapLink(uint32_t idx, uint32_t tgt_idx);

        /** Original size of the set. */
        inline uint32_t getSourceSize();

        inline bool isReallyActive(index_t idx);
        inline bool isActuallyActive(index_t idx);

        inline bool nextHypothesis(uint32_t level);
        /** Recover for usage the next available hypothesis at a given level.
         * @warning Works as an iterator on the hypotheses at the given level. */
        inline HypothesisT& getHypothesis();

        /** Internally selects hypotheses to skip according to a model. */
        inline void modelCleanUp(const ModelT& model, uint32_t level);
    };

    template<class SolverT>
    inline uint32_t HypothesesSet<SolverT>::getSourceSize() {
        return hp_active.get_maximal_size();
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::mapHypothesis(uint32_t idx, HypothesisT* hyp) {
        hp_mapping[idx] = hyp;
    }
    template<class SolverT>
    inline void HypothesesSet<SolverT>::mapLink(uint32_t idx, uint32_t tgt_idx) {
        hp_links[idx].push_back(tgt_idx);
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::accessLevel(uint32_t level) {
        if (level > clevel) increaseLevel(level);
        else                decreaseLevel(level);
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::increaseLevel(uint32_t target) {
        while (clevel < target) {
            /* TODO: Fixme.
               The hack +1 to is necessary to access the first active when asking
               to get downward. However, this is tragically unsafe.
               Which is why we add a min to unsure we do not make oob accesses later.
            */
#define MIN(a,b) (a) < (b) ? (a) : (b)
            pointer[clevel + 1] = MIN(hp_active.get_last() + 1, hp_active.get_maximal_size());
            limit[clevel + 1] = pointer[clevel];
            ++clevel;
        }
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::decreaseLevel(uint32_t target) {
        while (clevel > target) {
            unselectLevel(clevel);
            --clevel;
        }
    }

    template<class SolverT>
    inline bool HypothesesSet<SolverT>::isReallyActive(index_t idx) {
        return hp_active.is_active(idx)
            && idx >= limit[clevel];
    }

    template<class SolverT>
    inline bool HypothesesSet<SolverT>::isActuallyActive(index_t idx) {
        level_t level = hp_active.get(idx);
        return hp_active.is_paused(idx)
            && clevel == level + 1
            && limit[clevel] > idx;
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::selectCurrentHypothesis() {
        index_t selected = pointer[clevel];
        if (hp_active.is_active(selected)) {
            selection_map[clevel].push_back(selected);
        } else if (hp_active.is_paused(selected)) {
            pselection_map[clevel].push_back(selected);
        } else { /* TODO: Error */ }
        hp_active.deactivate(selected);
        for (index_t linked : hp_links[selected]) {
            if (hp_active.is_active(linked)) {
                hp_active.deactivate(linked);
                selection_map[clevel].push_back(linked);
            } else if (hp_active.is_paused(linked)) {
                hp_active.deactivate(linked);
                pselection_map[clevel].push_back(linked);
            }
        }
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::unselectLevel(uint32_t level) {
        for (index_t skipped : selection_map[level]) {
            hp_active.activate(skipped);
        }
        for (index_t skipped : pselection_map[level]) {
            hp_active.pause(skipped);
        }
        selection_map[level].clear();
        pselection_map[level].clear();
    }

    template<class SolverT>
    inline bool HypothesisSkipper<SolverT>::canBeSkipped(typename SolverT::HypothesisT& h, uint32_t level) {
        return solver.currentlySubsumed(h, actives.storage, level);
    }

    template<class SolverT>
    inline bool HypothesesSet<SolverT>::nextHypothesis(uint32_t level) {
        accessLevel(level);
        unselectLevel(clevel);
        while (true) {
            index_t next = hp_active.get_downward(pointer[clevel]);
            if (next != pointer[clevel]) {
                pointer[clevel] = next;
                instrument::analyze(&next, instrument::analyze_type::pre_select);
                if (!skipper.canBeSkipped(*hp_mapping[pointer[clevel]], clevel)) {
                    if (isReallyActive(pointer[clevel]) || isActuallyActive(pointer[clevel])) {
                        return true;
                    }
                }
            } else {
                return false;
            }
        }
    }

    template<class SolverT>
    inline typename SolverT::HypothesisT& HypothesesSet<SolverT>::getHypothesis() {
        selectCurrentHypothesis();
        return *hp_mapping[pointer[clevel]];
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::modelCleanUp(const ModelT& model, uint32_t level) {
        accessLevel(level);
        for (index_t idx : hp_active) {
            if (!hp_active.is_active(idx)) continue;
            if (model.isSkippable(*hp_mapping[idx])) {
                hp_active.pause(idx);
                hp_active.set(idx, clevel);
                selection_map[clevel-1].push_back(idx);
                instrument::analyze(&idx, instrument::analyze_type::model_skip);
            }
        }
    }

};

#endif
