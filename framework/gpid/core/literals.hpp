/**
 * \file gpid/core/literals.hpp
 * \brief GPiD-Framework Literals handling related classes.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__LITERALS_HPP
#define GPID_FRAMEWORK__CORE__LITERALS_HPP

#include <list>
#include <sstream>
#include <starray/starray.hpp>
#include <gpid/errors.hpp>
#include <gpid/core/solvers.hpp>
#include <gpid/util/skipper_controller.hpp>
#include <gpid/util/storage.hpp>

#include <gpid/instrument/instrument.hpp>

namespace gpid {

    template<class LiteralT>
    class LiteralHypothesis {
    public:
        typedef uint32_t index_t;
    private:
        starray::SequentialActivableArray _array;
        std::map<uint32_t, std::vector<index_t>> _lmapping;
    public:
        LiteralHypothesis(uint32_t size) : _array(size) {
            for (uint32_t i = 0; i < size; ++i) _array.deactivate(i);
        }

        inline void addLiteral(index_t lidx, uint32_t lkey) {
            _array.activate(lidx);
            _lmapping[lkey].push_back(lidx);
        }
        inline void removeLiterals(uint32_t lkey) {
            for (index_t lidx : _lmapping[lkey]) {
                _array.deactivate(lidx);
            }
            _lmapping[lkey].clear();
        }

        typedef typename starray::SequentialActivableArray::iterator iterator;
        typedef typename starray::SequentialActivableArray::const_iterator const_iterator;
        inline iterator begin() { return _array.begin(); }
        inline iterator end() { return _array.end(); }
        inline const_iterator cbegin() { return _array.cbegin(); }
        inline const_iterator cend() { return _array.cend(); }
    };

    /** \brief Class for deciding on skipping literals. */
    template<class SolverT>
    class LiteralSkipper {
        typedef typename SolverT::LiteralT LiteralT;
        SolverT& solver;
        AbducibleTree<SolverT>& storage;
        LiteralMapper<LiteralT>& mapper;
        SkipperController& control;
        struct {
            uint64_t storage     = 0;
            uint64_t level_depth = 0;
            uint64_t consistency = 0;
            uint64_t consequence = 0;
        } counters;
    public:
        LiteralSkipper(SolverT& s, AbducibleTree<SolverT>& st,
                       LiteralMapper<LiteralT>& m, SkipperController& ctrler)
            : solver(s), storage(st), mapper(m), control(ctrler) {}

        typedef typename LiteralMapper<typename SolverT::LiteralT>::index_t LiteralRefT;
        /** \brief Decide if an literal can be skipped at a given level. */
        inline bool canBeSkipped(LiteralRefT h, uint32_t level);
        /** \brief Decide if an literal is consistent with active ones. */
        inline bool consistent(LiteralRefT h, uint32_t level);
        inline void storeCounts(std::map<std::string, uint64_t>& target);
    };

    /** \brief Class for handling abducible literals. \ingroup gpidcorelib */
    template<class SolverT>
    class LiteralsEngine {
    public:
        typedef typename SolverT::LiteralT LiteralT;
        typedef typename SolverT::ModelT ModelT;
    private:
        SolverT& solver;
        AbducibleTree<SolverT> storage;
        LiteralHypothesis<LiteralT> hypothesis;

        typedef uint32_t index_t;
        typedef uint32_t level_t;
        starray::SequentialActivableArray      l_active;
        LiteralMapper<LiteralT>                l_mapper;
        std::map<index_t, std::list<index_t> > l_links;

        LiteralSkipper<SolverT> skipper;

        std::map<level_t, std::list<index_t> > selection_map;
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

        inline void deactivateLiteral(index_t idx, level_t level);
        inline void deactivateSequents(index_t ub, level_t level);

        inline LiteralT& getLiteral(index_t idx);
        inline index_t getCurrentIndex();
    public:
        LiteralsEngine(SolverT& solver, SkipperController& ctrler, uint32_t size)
            : solver(solver), storage(solver), hypothesis(size), l_active(size),
              skipper(solver, storage, l_mapper, ctrler), clevel(1)
        { limit[1] = 0; pointer[1] = size; }
        /** Map an index of the set to a specific literal. */
        inline void mapLiteral(uint32_t idx, LiteralT* hyp);
        /** Specify incompatible literals. */
        inline void mapLink(uint32_t idx, uint32_t tgt_idx);

        /** Original size of the set. */
        inline uint32_t getSourceSize();
        inline std::map<std::string, uint64_t>& getSkippedCounts();

        inline SolverTestStatus testHypothesis(uint32_t level);

        inline void printCurrentImplicate();
        inline void printStorage();
        inline void exportStorage();

        /**
         * \brief Find the next non tested literal.
         * \param level Level to look for literals at.
         * \return true iff there exists a valid non-tested literal at level level.
         *
         * If such an literal exists, this method will also position the
         * internal literal pointer on it, allowing the selected literal
         * to be accessed/recovered via the \ref getLiteral method.
         */
        inline bool nextLiteral(uint32_t level);
        inline void selectCurrentLiteral();
        inline LiteralT& getCurrentLiteral();

        inline void backtrack(uint32_t level);

        /** Internally selects literals to skip according to a model. */
        inline void modelCleanUp(uint32_t level);

        inline void storeCurrentImplicate();
    };

    template<class SolverT>
    inline uint32_t LiteralsEngine<SolverT>::getSourceSize() {
        return l_active.get_maximal_size();
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::mapLiteral(uint32_t idx, LiteralT* hyp) {
        l_mapper.map(idx, hyp);
    }
    template<class SolverT>
    inline void LiteralsEngine<SolverT>::mapLink(uint32_t idx, uint32_t tgt_idx) {
        l_links[idx].push_back(tgt_idx);
    }

    template<class SolverT>
    inline void LiteralSkipper<SolverT>::storeCounts(std::map<std::string, uint64_t>& target) {
        target["storage"]      = counters.storage;
        target["level depth"]  = counters.level_depth;
        target["consistency"]  = counters.consistency;
        target["consequences"] = counters.consequence;
    }
    template<class SolverT>
    inline std::map<std::string, uint64_t>& LiteralsEngine<SolverT>::getSkippedCounts() {
        skipper.storeCounts(counts_wrap);
        return counts_wrap;
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::printCurrentImplicate() {
        solver.printHypothesisNegation();
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::printStorage() {
        storage.print();
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::exportStorage() {
        snlog::l_warn("TODO: Do not write storage graph on stdout but on parametrized file");
        storage.exportGraph(std::cout);
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::accessLevel(uint32_t level) {
        if (level > clevel) increaseLevel(level);
        else                decreaseLevel(level);
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::deactivateLiteral(index_t idx, level_t level) {
        if (l_active.is_active(idx)) {
            selection_map[level].push_back(idx);
        } else if (l_active.is_paused(idx)) {
            pselection_map[level].push_back(idx);
        }
        l_active.deactivate(idx);
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::increaseLevel(uint32_t target) {
        while (clevel < target) {
            /* TODO: Fixme.
               The hack +1 to is necessary to access the first active when asking
               to get downward. However, this is tragically unsafe.
               Which is why we add a min to unsure we do not make oob accesses later.
            */
#define MIN(a,b) (a) < (b) ? (a) : (b)
            pointer[clevel + 1] = MIN(l_active.get_last() + 1, l_active.get_maximal_size());
            limit[clevel + 1] = getCurrentIndex();
            ++clevel;
        }
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::decreaseLevel(uint32_t target) {
        while (clevel > target) {
            unselectLevel(clevel);
            --clevel;
        }
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::deactivateSequents(index_t ub, level_t level) {
        index_t curr = ub;
        index_t next = l_active.get_downward(curr);
        while (curr != next) {
            curr = next;
            if (l_active.is_active(curr)) {
                l_active.deactivate(curr);
                selection_map[level].push_back(curr);
            }
            if (l_active.is_paused(curr) && l_active.get(curr) != level) {
                l_active.deactivate(curr);
                pselection_map[level].push_back(curr);
            }
            next = l_active.get_downward(curr);
        }
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::selectCurrentLiteral() {
        index_t selected = getCurrentIndex();
        deactivateLiteral(selected, clevel);
        for (index_t linked : l_links[selected]) {
            deactivateLiteral(linked, clevel);
        }
        deactivateSequents(selected, clevel);
        solver.addLiteral(getCurrentLiteral(), clevel);
        hypothesis.addLiteral(getCurrentIndex(), clevel);
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::unselectLevel(uint32_t level) {
        hypothesis.removeLiterals(level);
        solver.removeLiterals(level);
        for (index_t skipped : selection_map[level]) {
            if (l_active.is_paused(skipped)) {
                l_active.set(skipped, pvalues_map[skipped].back());
                pvalues_map[skipped].pop_back();
            }
            l_active.activate(skipped);
        }
        for (index_t skipped : pselection_map[level]) {
            l_active.pause(skipped);
        }
        selection_map[level].clear();
        pselection_map[level].clear();
    }

    template<class SolverT>
    inline bool LiteralSkipper<SolverT>::consistent(LiteralRefT h, uint32_t level) {
        solver.addLiteral(mapper.get(h), level+1);
        SolverTestStatus status = solver.checkConsistency(level+1);
        if (status == SolverTestStatus::SOLVER_UNKNOWN) {
            throw UndecidableProblemError("Solver could not decide consistency query");
        }
        solver.removeLiterals(level+1);
        return status == SolverTestStatus::SOLVER_SAT;
    }

    template<class SolverT>
    inline bool LiteralSkipper<SolverT>::canBeSkipped(LiteralRefT h, uint32_t level) {
        if (control.consequences && solver.isConsequence(mapper.get(h), level)) {
            counters.consequence++;
            return true;
        }
        if (control.storage && storage.fwdSubsumes(h)) {
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
    inline void LiteralsEngine<SolverT>::backtrack(uint32_t level) {
        solver.removeLiterals(level);
    }

    template<class SolverT>
    inline bool LiteralsEngine<SolverT>::nextLiteral(uint32_t level) {
        accessLevel(level);
        unselectLevel(clevel);
        while (true) {
            index_t next = l_active.get_downward(getCurrentIndex());
            if (next != getCurrentIndex()) {
                pointer[clevel] = next;
                insthandle(instrument::idata(getLiteral(next).str()),
                           instrument::instloc::pre_select);
                if (!skipper.canBeSkipped(getCurrentIndex(), clevel)) {
                    if (!l_active.is_paused(getCurrentIndex())
                        || l_active.get(getCurrentIndex()) != clevel) {
                        return true;
                    }
                }
            } else {
                return false;
            }
        }
    }

    template<class SolverT>
    inline typename SolverT::LiteralT& LiteralsEngine<SolverT>::getLiteral(index_t idx) {
        return l_mapper.get(idx);
    }

    template<class SolverT>
    inline typename LiteralsEngine<SolverT>::index_t LiteralsEngine<SolverT>::getCurrentIndex() {
        return pointer[clevel];
    }

    template<class SolverT>
    inline typename SolverT::LiteralT& LiteralsEngine<SolverT>::getCurrentLiteral() {
        return getLiteral(getCurrentIndex());
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::modelCleanUp(uint32_t level) {
        accessLevel(level);
        const ModelT& model = solver.recoverModel();
        for (index_t idx : l_active) {
            if (!l_active.is_active(idx)) continue;
            if (model.isSkippable(getLiteral(idx))) {
                l_active.pause(idx);
                pvalues_map[idx].push_back(l_active.get(idx));
                l_active.set(idx, clevel);
                selection_map[clevel-1].push_back(idx);
                insthandle(instrument::idata(getLiteral(idx).str()),
                           instrument::instloc::model_skip);
            }
        }
    }

    template<class SolverT>
    inline void LiteralsEngine<SolverT>::storeCurrentImplicate() {
        snlog::l_warn("**indev : Storage");
        /* TODO: STORAGE */
    }

    template<class SolverT>
    inline SolverTestStatus LiteralsEngine<SolverT>::testHypothesis(uint32_t level) {
        accessLevel(level);
        insthandle(instrument::idata(solver.hypothesisAsString()), instrument::ismt_test);
        SolverTestStatus status = solver.testHypothesis(level);
        insthandle(instrument::idata(status), instrument::ismt_result);
        return status;
    }

};

#endif
