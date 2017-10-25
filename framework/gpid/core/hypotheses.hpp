#ifndef GPID_HYPOTHESES_HPP
#define GPID_HYPOTHESES_HPP

#include <map>
#include <list>
#include <starray/starray.hpp>
#include <snlog/snlog.hpp>

namespace gpid {

    template<class SolverT>
    class HypothesisSkipper {
        SolverT& solver;
    public:
        HypothesisSkipper(SolverT& s) : solver(s) {}

        inline bool canBeSkipped(typename SolverT::HypothesisT& h);
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

        std::map<level_t, index_t> limit;
        std::map<level_t, index_t> pointer;
        level_t clevel;

        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);

        inline void unselectLevel(level_t level);

        inline void selectCurrentHypothesis();
    public:
        HypothesesSet(SolverT& solver, uint32_t size)
            : skipper(solver), hp_active(size), clevel(1)
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
        /** Skip available hypotheses if induced by the active model or stored implicates
         * @return false if and only if all possible hypotheses have been skipped. */
        inline bool skipSkippables(SolverT& storage, bool with_storage, level_t level);
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
    inline void HypothesesSet<SolverT>::selectCurrentHypothesis() {
        index_t selected = pointer[clevel];
        hp_active.deactivate(selected);
        selection_map[clevel].push_back(selected);
        for (index_t linked : hp_links[selected]) {
            hp_active.deactivate(linked);
            selection_map[clevel].push_back(linked);
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
    inline bool HypothesesSet<SolverT>::nextHypothesis(uint32_t level) {
        accessLevel(level);
        unselectLevel(clevel);
        index_t next = hp_active.get_downward(pointer[clevel]);
        if (next != pointer[clevel]) {
            pointer[clevel] = next;
            return pointer[clevel] >= limit[clevel];
        } else {
            return false;
        }
    }

    template<class SolverT>
    inline typename SolverT::HypothesisT& HypothesesSet<SolverT>::getHypothesis() {
        selectCurrentHypothesis();
        return *hp_mapping[pointer[clevel]];
    }

    template<class SolverT>
    inline bool HypothesesSet<SolverT>::skipSkippables(SolverT& solver, bool with_storage, level_t level) {
        snlog::l_warn("Not reimplemented"); // TODO : REDO
        return true;
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::modelCleanUp(const ModelT& model, uint32_t level) {
        snlog::l_warn("Not reimplemented"); // TODO : REDO
    }

};

#endif
