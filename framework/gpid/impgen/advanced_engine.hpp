/**
 * \file gpid/impgen/advanced_engine.hpp
 * \brief GPiD-Framework Advanced Abducible Engine for Implicate Generation.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__IMPGEN__ADVANCED_ENGINE_HPP
#define GPID_FRAMEWORK__IMPGEN__ADVANCED_ENGINE_HPP

#include <list>

#include <starray/starray.hpp>

#include <gpid/core/errors.hpp>
#include <gpid/core/memory.hpp>
#include <gpid/sai/saitypes.hpp>
#include <gpid/storage/atrees.hpp>
#include <gpid/impgen/skipcontrol.hpp>
#include <gpid/instrument/instrument.hpp>

namespace gpid {

    class LiteralHypothesis {
    public:
        typedef uint32_t index_t;
    private:
        starray::SequentialActivableArray _array;
        std::map<uint32_t, std::vector<index_t>> _lmapping;
    public:
        LiteralHypothesis(uint32_t size) : _array(size)
        { for (uint32_t i = 0; i < size; ++i) _array.deactivate(i); }

        inline void addLiteral(index_t lidx, uint32_t lkey);
        inline void removeLiterals(uint32_t lkey);

        typedef typename starray::SequentialActivableArray::iterator iterator;
        typedef typename starray::SequentialActivableArray::const_iterator const_iterator;
        inline       iterator begin()  { return _array.begin();  }
        inline       iterator end()    { return _array.end();    }
        inline const_iterator cbegin() { return _array.cbegin(); }
        inline const_iterator cend()   { return _array.cend();   }

        template<typename InterfaceT> friend class LiteralHypothesisPrinter;
    };

    template<typename InterfaceT> class LiteralHypothesisPrinter;
    template<typename InterfaceT> std::ostream& operator<<
    (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT>& hlp);

    template<typename InterfaceT>
    class LiteralHypothesisPrinter {
        LiteralHypothesis& hypothesis;
        ObjectMapper<typename InterfaceT::LiteralT>& mapper;
        bool negate;
    public:
        LiteralHypothesisPrinter
        (LiteralHypothesis& lh, ObjectMapper<typename InterfaceT::LiteralT>& mp, bool neg=true)
            : hypothesis(lh), mapper(mp), negate(neg) {}
        LiteralHypothesisPrinter(const LiteralHypothesisPrinter<InterfaceT>& o)
            : hypothesis(o.hypothesis), mapper(o.mapper), negate(o.negate) {}

        friend std::ostream& operator<< <InterfaceT>
        (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT>& hlp);
    };

    /** \brief Class for handling abducible literals. \ingroup gpidcorelib */
    template<class InterfaceT>
    class AdvancedAbducibleEngine {
    public:
        using LiteralT = typename InterfaceT::LiteralT;
        using ModelT = typename InterfaceT::ModelT;
        using counter_t = uint64_t;
    private:
        SolverInterfaceEngine<InterfaceT> interfaceEngine;
        InterfaceT& solver;

        using index_t = uint32_t;
        using level_t = uint32_t;
        starray::SequentialActivableArray lactive;
        ObjectMapper<LiteralT> lmapper;
        using LiteralReference = typename ObjectMapper<LiteralT>::index_t;
        std::map<index_t, std::list<index_t> > llinks;

        AbducibleTree<InterfaceT, LiteralHypothesis> storage;
        LiteralHypothesis hypothesis;

        SkipController& skipctrl;
        struct {
            counter_t storage     = 0;
            counter_t level_depth = 0;
            counter_t consistency = 0;
            counter_t consequence = 0;
        } skip_counters;

        std::map<level_t, std::list<index_t> > selection_map;
        std::map<level_t, std::list<index_t> > pselection_map;

        std::map<index_t, std::list<level_t> > pvalues_map;

        std::map<level_t, index_t> limit;
        std::map<level_t, index_t> pointer;
        level_t clevel;

        std::map<std::string, counter_t> counts_wrap;

        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);

        inline void unselectLevel(level_t level);

        inline void deactivateLiteral(index_t idx, level_t level);
        inline void deactivateSequents(index_t ub, level_t level);

        /** \brief Decide if an literal can be skipped at a given level. */
        inline bool canBeSkipped(LiteralReference h, level_t level);
        /** \brief Decide if an literal is consistent with active ones. */
        inline bool isConsistent(LiteralReference h, level_t level);

        inline LiteralT& getLiteral(index_t idx);
        inline index_t getCurrentIndex();
    public:
        AdvancedAbducibleEngine(size_t size)
            : lactive(size), storage(lmapper), hypothesis(size), clevel(1)
        { limit[1] = 0; pointer[1] = size; }
        /** Map an index of the set to a specific literal. */
        inline void mapLiteral(uint32_t idx, LiteralT* hyp);
        /** Specify incompatible literals. */
        inline void mapLink(uint32_t idx, uint32_t tgt_idx);

        /** Original size of the set. */
        inline uint32_t getSourceSize();
        inline std::map<std::string, counter_t>& getSkippedCounts();

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
        inline bool searchNextLiteral(uint32_t level);
        inline void selectCurrentLiteral();
        inline LiteralT& getCurrentLiteral();

        inline void backtrack(uint32_t level);

        /** Internally selects literals to skip according to a model. */
        inline void modelCleanUp(uint32_t level);

        inline void storeCurrentImplicate();
    };

    /* *** Implementations *** */

    inline void LiteralHypothesis::addLiteral(index_t lidx, uint32_t lkey) {
        _array.activate(lidx);
        _lmapping[lkey].push_back(lidx);
    }

    inline void LiteralHypothesis::removeLiterals(uint32_t lkey) {
        for (index_t lidx : _lmapping[lkey]) {
            _array.deactivate(lidx);
        }
        _lmapping[lkey].clear();
    }

    template<typename InterfaceT>
    inline const LiteralHypothesisPrinter<InterfaceT> implicate
    (LiteralHypothesis& h, ObjectMapper<typename InterfaceT::LiteralT>& mp) {
        return LiteralHypothesisPrinter<InterfaceT>(h, mp, true);
    }

    template<typename InterfaceT>
    inline const LiteralHypothesisPrinter<InterfaceT> hypothesis
    (LiteralHypothesis& h, ObjectMapper<typename InterfaceT::LiteralT>& mp) {
        return LiteralHypothesisPrinter<InterfaceT>(h, mp, false);
    }

    template<typename InterfaceT> std::ostream& operator<<
    (std::ostream& os, const LiteralHypothesisPrinter<InterfaceT>& hlp) {
        return InterfaceT::to_stream(os, hlp.begin());
    }

    template<typename Printable>
    inline void print_item(Printable& p) {
        std::cout << "> " << p << std::endl;
    }

    template<typename InterfaceT>
    inline uint32_t AdvancedAbducibleEngine<InterfaceT>::getSourceSize() {
        return lactive.get_maximal_size();
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::mapLiteral(uint32_t idx, LiteralT* hyp) {
        lmapper.map(idx, hyp);
    }
    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::mapLink(uint32_t idx, uint32_t tgt_idx) {
        llinks[idx].push_back(tgt_idx);
    }

    template<typename InterfaceT>
    inline std::map<std::string, uint64_t>& AdvancedAbducibleEngine<InterfaceT>::getSkippedCounts() {
        counts_wrap["storage"]      = skip_counters.storage;
        counts_wrap["level depth"]  = skip_counters.level_depth;
        counts_wrap["consistency"]  = skip_counters.consistency;
        counts_wrap["consequences"] = skip_counters.consequence;
        return counts_wrap;
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::printCurrentImplicate() {
        print_item(implicate(hypothesis, lmapper));
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::printStorage() {
        storage.print();
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::exportStorage() {
        snlog::l_warn("TODO: Do not write storage graph on stdout but on parametrized file");
        storage.exportGraph(std::cout);
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::accessLevel(uint32_t level) {
        if (level > clevel) increaseLevel(level);
        else                decreaseLevel(level);
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::deactivateLiteral(index_t idx, level_t level) {
        if (lactive.is_active(idx)) {
            selection_map[level].push_back(idx);
        } else if (lactive.is_paused(idx)) {
            pselection_map[level].push_back(idx);
        }
        lactive.deactivate(idx);
    }

#define MIN(a,b) (a) < (b) ? (a) : (b)
    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::increaseLevel(uint32_t target) {
        while (clevel < target) {
            /* TODO: Fixme.
               The hack +1 to is necessary to access the first active when asking
               to get downward. However, this is tragically unsafe.
               Which is why we add a min to unsure we do not make oob accesses later.
            */
            pointer[clevel + 1] = MIN(lactive.get_last() + 1, lactive.get_maximal_size());
            limit[clevel + 1] = getCurrentIndex();
            ++clevel;
        }
    }
#undef MIN

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::decreaseLevel(uint32_t target) {
        while (clevel > target) {
            unselectLevel(clevel);
            --clevel;
        }
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::deactivateSequents(index_t ub, level_t level) {
        index_t curr = ub;
        index_t next = lactive.get_downward(curr);
        while (curr != next) {
            curr = next;
            if (lactive.is_active(curr)) {
                lactive.deactivate(curr);
                selection_map[level].push_back(curr);
            }
            if (lactive.is_paused(curr) && lactive.get(curr) != level) {
                lactive.deactivate(curr);
                pselection_map[level].push_back(curr);
            }
            next = lactive.get_downward(curr);
        }
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::selectCurrentLiteral() {
        index_t selected = getCurrentIndex();
        deactivateLiteral(selected, clevel);
        for (index_t linked : llinks[selected]) {
            deactivateLiteral(linked, clevel);
        }
        deactivateSequents(selected, clevel);
        solver.addLiteral(getCurrentLiteral(), clevel);
        hypothesis.addLiteral(getCurrentIndex(), clevel);
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::unselectLevel(uint32_t level) {
        hypothesis.removeLiterals(level);
        solver.removeLiterals(level);
        for (index_t skipped : selection_map[level]) {
            if (lactive.is_paused(skipped)) {
                lactive.set(skipped, pvalues_map[skipped].back());
                pvalues_map[skipped].pop_back();
            }
            lactive.activate(skipped);
        }
        for (index_t skipped : pselection_map[level]) {
            lactive.pause(skipped);
        }
        selection_map[level].clear();
        pselection_map[level].clear();
    }

    template<typename InterfaceT>
    inline bool AdvancedAbducibleEngine<InterfaceT>::isConsistent(LiteralReference h, uint32_t level) {
        solver.addLiteral(lmapper.get(h), level+1);
        SolverTestStatus status = solver.checkConsistency(level+1);
        if (status == SolverTestStatus::UNKNOWN) {
            throw UndecidableProblemError("Solver could not decide consistency query");
        }
        solver.removeLiterals(level+1);
        return status == SolverTestStatus::SAT;
    }

    template<typename InterfaceT>
    inline bool AdvancedAbducibleEngine<InterfaceT>::canBeSkipped(LiteralReference h, uint32_t level) {
        if (skipctrl.max_level <= level) {
            skip_counters.level_depth++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":depth"),
                       instrument::instloc::skip);
            return true;
        }
        if (skipctrl.consequences && solver.isConsequence(lmapper.get(h), level)) {
            skip_counters.consequence++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":consequence"),
                       instrument::instloc::skip);
            return true;
        }
        if (skipctrl.storage && storage.fwdSubsumes(hypothesis, h)) {
            skip_counters.storage++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":storage"),
                       instrument::instloc::skip);
            return true;
        }
        if (!skipctrl.inconsistencies && !consistent(h, level)) {
            skip_counters.consistency++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":consistency"),
                       instrument::instloc::skip);
            return true;
        }
        return false;
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::backtrack(uint32_t level) {
        solver.removeLiterals(level);
    }

    template<typename InterfaceT>
    inline bool AdvancedAbducibleEngine<InterfaceT>::searchNextLiteral(uint32_t level) {
        accessLevel(level);
        unselectLevel(clevel);
        while (true) {
            index_t next = lactive.get_downward(getCurrentIndex());
            if (next != getCurrentIndex()) {
                pointer[clevel] = next;
                insthandle(instrument::idata(getLiteral(next).str()),
                           instrument::instloc::pre_select);
                if (!canBeSkipped(getCurrentIndex(), clevel)) {
                    if (!lactive.is_paused(getCurrentIndex())
                        || lactive.get(getCurrentIndex()) != clevel) {
                        return true;
                    }
                }
            } else {
                return false;
            }
        }
    }

    template<typename InterfaceT>
    inline typename InterfaceT::LiteralT&
    AdvancedAbducibleEngine<InterfaceT>::getLiteral(index_t idx) {
        return lmapper.get(idx);
    }

    template<typename InterfaceT>
    inline typename AdvancedAbducibleEngine<InterfaceT>::index_t
    AdvancedAbducibleEngine<InterfaceT>::getCurrentIndex() {
        return pointer[clevel];
    }

    template<typename InterfaceT>
    inline typename InterfaceT::LiteralT&
    AdvancedAbducibleEngine<InterfaceT>::getCurrentLiteral() {
        return getLiteral(getCurrentIndex());
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::modelCleanUp(uint32_t level) {
        accessLevel(level);
        const ModelT& model = solver.recoverModel();
        for (index_t idx : lactive) {
            if (!lactive.is_active(idx)) continue;
            if (model.implies(getLiteral(idx))) {
                lactive.pause(idx);
                pvalues_map[idx].push_back(lactive.get(idx));
                lactive.set(idx, clevel);
                selection_map[clevel-1].push_back(idx);
                insthandle(instrument::idata(getLiteral(idx).str() + ":model"),
                           instrument::instloc::skip);
            }
        }
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::storeCurrentImplicate() {
        storage.bwdSubsumesRemove(hypothesis);
        storage.insert(hypothesis);
    }

    template<typename InterfaceT>
    inline SolverTestStatus AdvancedAbducibleEngine<InterfaceT>::testHypothesis(uint32_t level) {
        accessLevel(level);
        insthandle(instrument::idata(solver.hypothesisAsString()), instrument::instloc::ismt_test);
        SolverTestStatus status = solver.testHypothesis(level);
        insthandle(instrument::idata(to_string(status)), instrument::instloc::ismt_result);
        return status;
    }

}

#endif
