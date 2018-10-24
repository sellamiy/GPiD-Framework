/**
 * \file gpid/impgen/advanced_engine.hpp
 * \brief GPiD-Framework Advanced Abducible Engine for Implicate Generation.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__IMPGEN__ADVANCED_ENGINE_HPP
#define GPID_FRAMEWORK__IMPGEN__ADVANCED_ENGINE_HPP

#include <list>
#include <fstream>

#include <gpid/core/memory.hpp>
#include <gpid/core/saitypes.hpp>
#include <gpid/storage/atrees.hpp>
#include <gpid/impgen/skipcontrol.hpp>
#include <gpid/instrument/instrument.hpp>

namespace gpid {

    /** Literal conjunction representation for the advanced abducible engine. */
    class LiteralHypothesis {
    public:
        /** Abducible indexing type. */
        typedef uint32_t index_t;
    private:
        starray::SequentialActivableArray _array;
        std::map<uint32_t, std::vector<index_t>> _lmapping;
    public:
        /** Initialize a literal conjunction of given maximal size. */
        LiteralHypothesis(uint32_t size) : _array(size)
        { for (uint32_t i = 0; i < size; ++i) _array.deactivate(i); }

        /** Add a literal by reference to the conjunction. */
        inline void addLiteral(index_t lidx, uint32_t lkey);
        /** Remove some literals from the conjunction. */
        inline void removeLiterals(uint32_t lkey);

        /** \return The current number of literals in the conjunction. */
        inline constexpr size_t size() const { return _array.get_activated_size(); }

        /** Iterator on the literal references of the conjunction. */
        typedef typename starray::SequentialActivableArray::iterator iterator;
        /** Const Iterator on the literal references of the conjunction. */
        typedef typename starray::SequentialActivableArray::const_iterator const_iterator;
        /** \return Iterator on the first literal reference of the conjunction. */
        inline       iterator begin()  { return _array.begin();  }
        /** \return Iterator past the last literal reference of the conjunction. */
        inline       iterator end()    { return _array.end();    }
        /** \return Const Iterator on the first literal reference of the conjunction. */
        inline const_iterator cbegin() { return _array.cbegin(); }
        /** \return Const Iterator past the last literal reference of the conjunction. */
        inline const_iterator cend()   { return _array.cend();   }
    };

    /** \brief Class for handling abducible literals. \ingroup gpidcorelib */
    template<class InterfaceT>
    class AdvancedAbducibleEngine {
    public:
        /** Context manager type of the underlying interface. */
        using ContextManagerT = typename InterfaceT::ContextManagerT;
        /** Literal type of the underlying interface. */
        using LiteralT = typename InterfaceT::LiteralT;
        /** Model type of the underlying interface. */
        using ModelT = typename InterfaceT::ModelT;
        /** Problem loading type of the underlying interface. */
        using ProblemLoaderT = typename InterfaceT::ProblemLoaderT;
        /** Element counter type. */
        using counter_t = uint64_t;
        /** Abducible indexing type. */
        using index_t = uint32_t;
        /** Internal depth indexing type. */
        using level_t = uint32_t;
    private:
        SolverInterfaceEngine<InterfaceT> interfaceEngine;
        InterfaceT& solver_contrads;
        InterfaceT& solver_consistency;

        starray::SequentialActivableArray lactive;
        ObjectMapper<LiteralT> lmapper;
        using LiteralReference = typename ObjectMapper<LiteralT>::index_t;
        std::map<index_t, std::list<index_t>> llinks;

        AbducibleTree<InterfaceT, LiteralHypothesis> storage;
        LiteralHypothesis hypothesis;

        SkipController skipctrl;
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

        inline void unselectLevel();

        inline void addSolverLiteral(index_t idx);
        inline void clearSolversCurrentLevel();

        inline void deactivateLiteral(index_t idx);
        inline void deactivateSequents(index_t ub);

        /** \brief Decide if an literal can be skipped at a given level. */
        inline bool canBeSkipped(LiteralReference h);
        /** \brief Decide if an literal is consistent with active ones. */
        inline bool isConsistent(LiteralReference h);

        inline bool isConsequence(LiteralReference h);

        inline LiteralT& getLiteral(index_t idx);
        inline index_t getCurrentIndex();
    public:
        /** Create an abducible engine. */
        AdvancedAbducibleEngine(size_t size, ContextManagerT& ctx, ImpgenOptions& iopts);
        /** Create an abducible engine. */
        template<typename AbducibleSource>
        AdvancedAbducibleEngine(AbducibleSource& source, ContextManagerT& ctx, ImpgenOptions& iopts);

        /** Reinitialize the abducible engine. */
        inline void reinit();
        /** Initialize the underlying solver interface with a given problem. */
        inline void initializeSolvers(ProblemLoaderT& pbld);

        /** Map an index of the set to a specific literal. */
        inline void mapLiteral(uint32_t idx, LiteralT* hyp);
        /** Specify incompatible literals. */
        inline void mapLink(uint32_t idx, uint32_t tgt_idx);

        /** Original size of the set. */
        inline constexpr uint32_t getSourceSize() const;
        /** Count of skipped candidates for various reasons. */
        inline std::map<std::string, counter_t>& getSkippedCounts();

        /** Check if the current hypothesis is a contradiction to the problem. */
        inline SolverTestStatus testHypothesis(uint32_t level);

        /** Print the current hypothesis in implicate format. */
        inline void printCurrentImplicate();
        /** Print the current implicate storage structure state. */
        inline void printStorage();
        /** Export the current implicate storage structure state. */
        inline void exportStorage(const std::string& filename);

        /**
         * \brief Find the next non tested literal.
         * \param level Depth to look for literals at.
         * \return true iff there exists a valid non-tested literal at depth level.
         *
         * If such an literal exists, this method will also position the
         * internal literal pointer on it, allowing the selected literal
         * to be accessed/recovered via the \ref getCurrentLiteral method.
         */
        inline bool searchNextLiteral(uint32_t level);
        /** Select the current literal in the hypothesis. */
        inline void selectCurrentLiteral();
        /** Recover the current literal. */
        inline LiteralT& getCurrentLiteral();

        /** Backtrack literal selections. */
        inline void backtrack(uint32_t level);

        /** Internally selects literals to skip according to a model. */
        inline void modelCleanUp();

        /** Insert the current hypothsis as an implicate in the storage structure. */
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
    AdvancedAbducibleEngine<InterfaceT>::AdvancedAbducibleEngine
    (size_t size, ContextManagerT& ctx, ImpgenOptions& iopts)
        : interfaceEngine(ctx),
          solver_contrads(interfaceEngine.newInterface()),
          solver_consistency(interfaceEngine.newInterface()),
          lactive(size),
          storage(interfaceEngine.newInterface(), lmapper),
          hypothesis(size),
          skipctrl(iopts)
    { reinit(); }

    template<typename InterfaceT>
    template<typename AbducibleSource>
    AdvancedAbducibleEngine<InterfaceT>::AdvancedAbducibleEngine
    (AbducibleSource& source, ContextManagerT& ctx, ImpgenOptions& iopts)
        : interfaceEngine(ctx),
          solver_contrads(interfaceEngine.newInterface()),
          solver_consistency(interfaceEngine.newInterface()),
          lactive(source.count()),
          lmapper(source.getMapper()),
          llinks(source.getLinks()),
          storage(interfaceEngine.newInterface(), lmapper),
          hypothesis(source.count()),
          skipctrl(iopts)
    { reinit(); }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::reinit() {
        clevel = 0;
        limit[0] = 0;
        pointer[0] = lactive.get_maximal_size();
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::initializeSolvers(ProblemLoaderT& pbld) {
        pbld.prepareReader();
        while (pbld.hasConstraint()) {
            solver_contrads.addConstraint(pbld.nextConstraint());
        }
    }

    template<typename InterfaceT>
    inline constexpr uint32_t AdvancedAbducibleEngine<InterfaceT>::getSourceSize() const {
        return lactive.get_maximal_size();
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::mapLiteral(index_t idx, LiteralT* hyp) {
        lmapper.map(idx, hyp);
    }
    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::mapLink(index_t idx, index_t tgt_idx) {
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
        printlh(implicate<InterfaceT>(hypothesis, lmapper, interfaceEngine.getContextManager()));
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::printStorage() {
        storage.print();
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::exportStorage(const std::string& filename) {
        std::ofstream outstr(filename);
        storage.exportGraph(outstr);
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::accessLevel(level_t level) {
        if (level > clevel) increaseLevel(level);
        else                decreaseLevel(level);
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::deactivateLiteral(index_t idx) {
        if (lactive.is_active(idx)) {
            selection_map[clevel].push_back(idx);
        } else if (lactive.is_paused(idx)) {
            pselection_map[clevel].push_back(idx);
        }
        lactive.deactivate(idx);
    }

/** Macro stress for the minimum of two things */
#define MIN(a,b) (a) < (b) ? (a) : (b)
    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::increaseLevel(level_t target) {
        while (clevel < target) {
            /* The hack +1 to is necessary to access the first active when
             * asking to get downward. However, this is tragically unsafe.
             * Which is why we add a min to unsure we do not make oob accesses
             * later. */
            pointer[clevel + 1] = MIN(lactive.get_last() + 1, lactive.get_maximal_size());
            limit[clevel + 1] = getCurrentIndex();
            solver_contrads.push();
            solver_consistency.push();
            ++clevel;
        }
    }
#undef MIN

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::decreaseLevel(level_t target) {
        while (clevel > target) {
            unselectLevel();
            solver_contrads.pop();
            solver_consistency.pop();
            --clevel;
        }
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::deactivateSequents(index_t ub) {
        index_t curr = ub;
        index_t next = lactive.get_downward(curr);
        while (curr != next) {
            curr = next;
            if (lactive.is_active(curr)) {
                lactive.deactivate(curr);
                selection_map[clevel].push_back(curr);
            }
            if (lactive.is_paused(curr) && lactive.get(curr) != clevel) {
                lactive.deactivate(curr);
                pselection_map[clevel].push_back(curr);
            }
            next = lactive.get_downward(curr);
        }
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::selectCurrentLiteral() {
        index_t selected = getCurrentIndex();
        deactivateLiteral(selected);
        for (index_t linked : llinks[selected]) {
            deactivateLiteral(linked);
        }
        deactivateSequents(selected);
        addSolverLiteral(getCurrentIndex());
        hypothesis.addLiteral(getCurrentIndex(), clevel);
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::addSolverLiteral(index_t idx) {
        solver_contrads.addLiteral(getLiteral(idx));
        solver_consistency.addLiteral(getLiteral(idx));
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::clearSolversCurrentLevel() {
        solver_contrads.pop();
        solver_contrads.push();
        solver_consistency.pop();
        solver_consistency.push();
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::unselectLevel() {
        hypothesis.removeLiterals(clevel);
        clearSolversCurrentLevel();
        for (index_t skipped : selection_map[clevel]) {
            if (lactive.is_paused(skipped)) {
                lactive.set(skipped, pvalues_map[skipped].back());
                pvalues_map[skipped].pop_back();
            }
            lactive.activate(skipped);
        }
        for (index_t skipped : pselection_map[clevel]) {
            lactive.pause(skipped);
        }
        selection_map[clevel].clear();
        pselection_map[clevel].clear();
    }

    template<typename InterfaceT>
    inline bool AdvancedAbducibleEngine<InterfaceT>::isConsistent(LiteralReference h) {
        solver_consistency.push();
        solver_consistency.addLiteral(lmapper.get(h));
        SolverTestStatus status = solver_consistency.check();
        if (status == SolverTestStatus::UNKNOWN) {
            throw UndecidableProblemError("Solver could not decide consistency query");
        }
        solver_consistency.pop();
        return status == SolverTestStatus::SAT;
    }

    template<typename InterfaceT>
    inline bool AdvancedAbducibleEngine<InterfaceT>::isConsequence(LiteralReference) {
        snlog::l_warn() << "isConsequence not implemented" << snlog::l_end; // TODO
        return false;
    }

    template<typename InterfaceT>
    inline bool AdvancedAbducibleEngine<InterfaceT>::canBeSkipped(LiteralReference h) {
        if (skipctrl.max_level <= clevel) {
            skip_counters.level_depth++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":depth"),
                       instrument::instloc::skip);
            return true;
        }
        if (skipctrl.consequences && isConsequence(h)) {
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
        if (!skipctrl.inconsistencies && !isConsistent(h)) {
            skip_counters.consistency++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":consistency"),
                       instrument::instloc::skip);
            return true;
        }
        return false;
    }

    template<typename InterfaceT>
    inline void AdvancedAbducibleEngine<InterfaceT>::backtrack(level_t level) {
        accessLevel(level);
        clearSolversCurrentLevel();
    }

    template<typename InterfaceT>
    inline bool AdvancedAbducibleEngine<InterfaceT>::searchNextLiteral(level_t level) {
        accessLevel(level);
        unselectLevel();
        while (true) {
            index_t next = lactive.get_downward(getCurrentIndex());
            if (next != getCurrentIndex()) {
                pointer[clevel] = next;
                insthandle(instrument::idata(getLiteral(next).str()),
                           instrument::instloc::pre_select);
                if (!canBeSkipped(getCurrentIndex())) {
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
    inline void AdvancedAbducibleEngine<InterfaceT>::modelCleanUp() {
        const ModelT& model = solver_contrads.getModel();
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
    inline SolverTestStatus AdvancedAbducibleEngine<InterfaceT>::testHypothesis(level_t level) {
        accessLevel(level);
        insthandle(instrument::idata(solver_consistency.getPrintableAssertions(false)),
                   instrument::instloc::ismt_test);
        SolverTestStatus status = solver_contrads.check();
        insthandle(instrument::idata(to_string(status)), instrument::instloc::ismt_result);
        return status;
    }

}

#endif
