/**
 * \file gpid/core/hypotheses.hpp
 * \brief GPiD-Framework Hypotheses handling related classes.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__HYPOTHESES_HPP
#define GPID_FRAMEWORK__CORE__HYPOTHESES_HPP

#include <map>
#include <list>
#include <starray/starray.hpp>
#include <snlog/snlog.hpp>
#include <gpid/core/solvers.hpp>
#include <gpid/util/skipper_controller.hpp>

#include <gpid/instrument/instrument.hpp>

namespace gpid {

    /** \brief Class for deciding on skipping hypotheses. */
    template<class SolverT>
    class HypothesisSkipper {
        SolverT& solver;
        SkipperController& control;
        struct {
            uint64_t storage     = 0;
            uint64_t level_depth = 0;
            uint64_t consistency = 0;
        } counters;
    public:
        HypothesisSkipper(SolverT& s, SkipperController& ctrler)
            : solver(s), control(ctrler) {}

        /** \brief Decide if an hypothesis can be skipped at a given level. */
        inline bool canBeSkipped(typename SolverT::HypothesisT& h, uint32_t level);
        /** \brief Decide if an hypothesis is consistent with active ones. */
        inline bool consistent(typename SolverT::HypothesisT& h, uint32_t level);
        inline void storeCounts(std::map<std::string, uint64_t>& target);
    };

    /** \brief Class for handling abducible hypotheses. \ingroup gpidcorelib */
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

        std::map<index_t, std::list<level_t> > pvalues_map;

        std::map<level_t, index_t> limit;
        std::map<level_t, index_t> pointer;
        level_t clevel;

        std::map<std::string, uint64_t> counts_wrap;

        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);

        inline void unselectLevel(level_t level);

        inline void deactivateHypothesis(index_t idx, level_t level);
        inline void deactivateSequents(index_t ub, level_t level);
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
        inline std::map<std::string, uint64_t>& getSkippedCounts();

        /**
         * \brief Find the next non tested hypothesis.
         * \param level Level to look for hypotheses at.
         * \return true iff there exists a valid non-tested hypothesis at level level.
         *
         * If such an hypothesis exists, this method will also position the
         * internal hypothesis pointer on it, allowing the selected hypothesis
         * to be accessed/recovered via the \ref getHypothesis method.
         */
        inline bool nextHypothesis(uint32_t level);
        /** Recover the hypothesis pointed by the internal pointer. \see nextHypothesis. */
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
    inline void HypothesisSkipper<SolverT>::storeCounts(std::map<std::string, uint64_t>& target) {
        target["storage"]     = counters.storage;
        target["level depth"] = counters.level_depth;
        target["consistency"] = counters.consistency;
    }
    template<class SolverT>
    inline std::map<std::string, uint64_t>& HypothesesSet<SolverT>::getSkippedCounts() {
        skipper.storeCounts(counts_wrap);
        return counts_wrap;
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::accessLevel(uint32_t level) {
        if (level > clevel) increaseLevel(level);
        else                decreaseLevel(level);
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::deactivateHypothesis(index_t idx, level_t level) {
        if (hp_active.is_active(idx)) {
            selection_map[level].push_back(idx);
        } else if (hp_active.is_paused(idx)) {
            pselection_map[level].push_back(idx);
        }
        hp_active.deactivate(idx);
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
    inline void HypothesesSet<SolverT>::deactivateSequents(index_t ub, level_t level) {
        index_t curr = ub;
        index_t next = hp_active.get_downward(curr);
        while (curr != next) {
            curr = next;
            if (hp_active.is_active(curr)) {
                hp_active.deactivate(curr);
                selection_map[level].push_back(curr);
            }
            if (hp_active.is_paused(curr) && hp_active.get(curr) != level) {
                hp_active.deactivate(curr);
                pselection_map[level].push_back(curr);
            }
            next = hp_active.get_downward(curr);
        }
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::selectCurrentHypothesis() {
        index_t selected = pointer[clevel];
        deactivateHypothesis(selected, clevel);
        for (index_t linked : hp_links[selected]) {
            deactivateHypothesis(linked, clevel);
        }
        deactivateSequents(selected, clevel);
    }

    template<class SolverT>
    inline void HypothesesSet<SolverT>::unselectLevel(uint32_t level) {
        for (index_t skipped : selection_map[level]) {
            if (hp_active.is_paused(skipped)) {
                hp_active.set(skipped, pvalues_map[skipped].back());
                pvalues_map[skipped].pop_back();
            }
            hp_active.activate(skipped);
        }
        for (index_t skipped : pselection_map[level]) {
            hp_active.pause(skipped);
        }
        selection_map[level].clear();
        pselection_map[level].clear();
    }

    template<class SolverT>
    inline bool HypothesisSkipper<SolverT>::consistent(typename SolverT::HypothesisT& h, uint32_t level) {
        solver.addHypothesis(h, level+1);
        SolverTestStatus status = solver.checkConsistency(level);
        if (status == SolverTestStatus::SOLVER_UNKNOWN) {
            snlog::l_fatal("Solver could not decide consistency query!");
        }
        solver.removeHypotheses(level+1);
        return status == SolverTestStatus::SOLVER_SAT;
    }

    template<class SolverT>
    inline bool HypothesisSkipper<SolverT>::canBeSkipped(typename SolverT::HypothesisT& h, uint32_t level) {
        if (control.storage && solver.storageSubsumed(h, level)) {
            counters.storage++;
            return true;
        }
        if (control.max_level <= level) {
            counters.level_depth++;
            return true;
        }
        if (!control.inconsistencies && !consistent(h, level)) {
            counters.consistency++;
            return true;
        }
        return false;
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
                    if (!hp_active.is_paused(pointer[clevel])
                        || hp_active.get(pointer[clevel]) != clevel) {
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
                pvalues_map[idx].push_back(hp_active.get(idx));
                hp_active.set(idx, clevel);
                selection_map[clevel-1].push_back(idx);
                instrument::analyze(&idx, instrument::analyze_type::model_skip);
            }
        }
    }

};

#endif
