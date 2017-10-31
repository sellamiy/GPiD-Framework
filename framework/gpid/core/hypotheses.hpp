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

        std::map<level_t, std::list<index_t> > selection_map;
        std::map<level_t, bool>                limit_predefs;

        std::map<level_t, index_t> limit;
        std::map<level_t, index_t> pointer;
        level_t clevel;

        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);

        inline void unselectLevel(level_t level);
        inline void predefineLimit(index_t idx, level_t level);

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
            if (!limit_predefs[clevel + 1]) {
                limit[clevel + 1] = pointer[clevel];
            }
            limit_predefs[clevel + 1] = false;
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
    inline void HypothesesSet<SolverT>::selectCurrentHypothesis() {
        index_t selected = pointer[clevel];
        hp_active.deactivate(selected);
        selection_map[clevel].push_back(selected);
        for (index_t linked : hp_links[selected]) {
            if (hp_active.is_active(linked)) {
                hp_active.deactivate(linked);
                selection_map[clevel].push_back(linked);
            }
        }
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::unselectLevel(uint32_t level) {
        for (index_t skipped : selection_map[level]) {
            hp_active.activate(skipped);
        }
        selection_map[level].clear();
    }

    template<class SolverT>
    inline bool HypothesisSkipper<SolverT>::canBeSkipped(typename SolverT::HypothesisT& h, uint32_t level) {
        return solver.currentlySubsumed(h, actives.storage, level);
    }

    template<class SolverT>
    inline bool HypothesesSet<SolverT>::nextHypothesis(uint32_t level) {
        accessLevel(level);
        unselectLevel(clevel);
        do {
            index_t next = hp_active.get_downward(pointer[clevel]);
            if (next != pointer[clevel]) {
                pointer[clevel] = next;
            } else {
                return false;
            }
            instrument::analyze(&next, instrument::analyze_type::pre_select);
        } while (skipper.canBeSkipped(*hp_mapping[pointer[clevel]], clevel));
        return pointer[clevel] >= limit[clevel];
    }

    template<class SolverT>
    inline typename SolverT::HypothesisT& HypothesesSet<SolverT>::getHypothesis() {
        selectCurrentHypothesis();
        return *hp_mapping[pointer[clevel]];
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::predefineLimit(index_t idx, level_t level) {
        limit[level] = idx;
        limit_predefs[level] = true;
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::modelCleanUp(const ModelT& model, uint32_t level) {
        accessLevel(level);
        for (index_t idx : hp_active) {
            if (!hp_active.is_active(idx)) continue;
            if (model.isSkippable(*hp_mapping[idx])) {
                if (idx >= pointer[clevel]) {
                    hp_active.deactivate(idx);
                    selection_map[clevel-1].push_back(idx);
                } else {
                    predefineLimit(idx, clevel + 1);
                }
                instrument::analyze(&idx, instrument::analyze_type::model_skip);
            } else {
                /*
                if (idx < pointer[clevel]) {
                    hp_active.deactivate(idx);
                    selection_map[clevel-1].push_back(idx);
                }
                */
            }
        }
    }

};

#endif
