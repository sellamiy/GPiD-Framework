/**
 * \file gpid/impgen/naive_engine.hpp
 * \brief GPiD-Framework Very Naive Abducible Engine for Implicate Generation.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__IMPGEN__NAIVE_ENGINE_HPP
#define GPID_FRAMEWORK__IMPGEN__NAIVE_ENGINE_HPP

#include <set>
#include <map>
#include <list>

#include <gpid/core/memory.hpp>
#include <gpid/core/saitypes.hpp>
#include <gpid/impgen/skipcontrol.hpp>
#include <gpid/instrument/instrument.hpp>
#include <gpid/utils/hprinters.hpp>

namespace gpid {

    /** Literal conjunction representation for the abducible engine. */
    class NaiveHypothesis {
    public:
        /** Abducible indexing type. */
        typedef uint32_t index_t;
    private:
        std::set<index_t> _conjunct;
        std::map<uint32_t, std::vector<index_t>> _lmapping;
    public:
        /** Initialize an empty literal conjunction. */
        NaiveHypothesis() {}

        /** Add a literal by reference to the conjunction. */
        inline void addLiteral(index_t lidx, uint32_t lkey);
        /** Remove some literals from the conjunction. */
        inline void removeLiterals(uint32_t lkey);

        /** \return The current number of literals in the conjunction. */
        inline size_t size() { return _conjunct.size(); }

        /** Iterator on the literal references of the conjunction. */
        typedef typename std::set<index_t>::iterator iterator;
        /** Const Iterator on the literal references of the conjunction. */
        typedef typename std::set<index_t>::const_iterator const_iterator;
        /** \return Iterator on the first literal reference of the conjunction. */
        inline       iterator begin()  { return _conjunct.begin();  }
        /** \return Iterator past the last literal reference of the conjunction. */
        inline       iterator end()    { return _conjunct.end();    }
        /** \return Const Iterator on the first literal reference of the conjunction. */
        inline const_iterator cbegin() { return _conjunct.cbegin(); }
        /** \return Const Iterator past the last literal reference of the conjunction. */
        inline const_iterator cend()   { return _conjunct.cend();   }
    };

    /** \brief Naive class for handling abducible literals. */
    template<class InterfaceT>
    class NaiveAbducibleEngine {
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

        ObjectMapper<LiteralT> lmapper;
        using LiteralReference = typename ObjectMapper<LiteralT>::index_t;
        std::map<index_t, std::list<index_t>> llinks;

        NaiveHypothesis hypothesis;

        SkipController skipctrl;
        struct {
            counter_t level_depth = 0;
            counter_t consistency = 0;
        } skip_counters;

        std::map<level_t, index_t> selection_map;
        index_t msize;
        level_t clevel;

        std::map<std::string, counter_t> counts_wrap;

        inline void increaseLevel(level_t target);
        inline void decreaseLevel(level_t target);
        inline void accessLevel(level_t level);

        inline void unselectLevel();

        inline void addSolverLiteral(index_t idx);
        inline void clearSolversCurrentLevel();

        inline bool isUnselected(index_t idx, level_t lvl);

        /** \brief Decide if an literal can be skipped at a given level. */
        inline bool canBeSkipped(LiteralReference h);
        /** \brief Decide if an literal is consistent with active ones. */
        inline bool isConsistent(LiteralReference h);

        inline LiteralT& getLiteral(index_t idx);
        inline index_t getCurrentIndex();
    public:
        /** Create an abducible engine. */
        NaiveAbducibleEngine(size_t size, ContextManagerT& ctx, ImpgenOptions& iopts);
        /** Create an abducible engine. */
        template<typename AbducibleSource>
        NaiveAbducibleEngine(AbducibleSource& source, ContextManagerT& ctx, ImpgenOptions& iopts);

        /** Reinitialize the abducible engine. */
        inline void reinit();
        /** Initialize the underlying solver interface with a given problem. */
        inline void initializeSolvers(ProblemLoaderT& pbld);

        /** Map an index of the set to a specific literal. */
        inline void mapLiteral(uint32_t idx, LiteralT* hyp);
        /** Specify incompatible literals. */
        inline void mapLink(uint32_t idx, uint32_t tgt_idx);

        /** Original size of the set. */
        inline uint32_t getSourceSize();
        /** Count of skipped candidates for various reasons. */
        inline std::map<std::string, counter_t>& getSkippedCounts();

        /** Check if the current hypothesis is a contradiction to the problem. */
        inline SolverTestStatus testHypothesis(uint32_t level);

        /** Print the current hypothesis in implicate format. */
        inline void printCurrentImplicate();
        /** Print the current implicate storage structure state. */
        inline void printStorage();
        /** Export the current implicate storage structure state. */
        inline void exportStorage(const std::string filename);

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

    inline void NaiveHypothesis::addLiteral(index_t lidx, uint32_t lkey) {
        _conjunct.insert(lidx);
        _lmapping[lkey].push_back(lidx);
    }

    inline void NaiveHypothesis::removeLiterals(uint32_t lkey) {
        for (index_t lidx : _lmapping[lkey]) {
            _conjunct.erase(lidx);
        }
        _lmapping[lkey].clear();
    }

    template<typename InterfaceT>
    NaiveAbducibleEngine<InterfaceT>::NaiveAbducibleEngine
    (size_t size, ContextManagerT& ctx, ImpgenOptions& iopts)
        : interfaceEngine(ctx),
          solver_contrads(interfaceEngine.newInterface()),
          solver_consistency(interfaceEngine.newInterface()),
          skipctrl(iopts),
          msize(size)
    { reinit(); }

    template<typename InterfaceT>
    template<typename AbducibleSource>
    NaiveAbducibleEngine<InterfaceT>::NaiveAbducibleEngine
    (AbducibleSource& source, ContextManagerT& ctx, ImpgenOptions& iopts)
        : interfaceEngine(ctx),
          solver_contrads(interfaceEngine.newInterface()),
          solver_consistency(interfaceEngine.newInterface()),
          lmapper(source.getMapper()),
          llinks(source.getLinks()),
          skipctrl(iopts),
          msize(source.count())
    { reinit(); }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::reinit() {
        clevel = 0;
        selection_map.clear();
        selection_map[0] = 0;
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::initializeSolvers(ProblemLoaderT& pbld) {
        pbld.prepareReader();
        while (pbld.hasConstraint()) {
            solver_contrads.addConstraint(pbld.nextConstraint());
        }
    }

    template<typename InterfaceT>
    inline uint32_t NaiveAbducibleEngine<InterfaceT>::getSourceSize() {
        return msize;
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::mapLiteral(index_t idx, LiteralT* hyp) {
        lmapper.map(idx, hyp);
    }
    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::mapLink(index_t idx, index_t tgt_idx) {
        llinks[idx].push_back(tgt_idx);
    }

    template<typename InterfaceT>
    inline std::map<std::string, uint64_t>& NaiveAbducibleEngine<InterfaceT>::getSkippedCounts() {
        counts_wrap["level depth"]  = skip_counters.level_depth;
        counts_wrap["consistency"]  = skip_counters.consistency;
        return counts_wrap;
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::printCurrentImplicate() {
        printlh(implicate<InterfaceT>(hypothesis, lmapper, interfaceEngine.getContextManager()));
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::printStorage() {
        snlog::l_internal("Storage not available in naive engine");
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::exportStorage(const std::string) {
        snlog::l_internal("Storage not available in naive engine");
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::accessLevel(level_t level) {
        if (level > clevel) increaseLevel(level);
        else                decreaseLevel(level);
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::increaseLevel(level_t target) {
        while (clevel < target) {
            /* TODO: Fixme.
               The hack +1 to is necessary to access the first active when asking
               to get downward. However, this is tragically unsafe.
               Which is why we add a min to unsure we do not make oob accesses later.
            */
            selection_map[clevel + 1] = 0;
            solver_contrads.push();
            solver_consistency.push();
            ++clevel;
        }
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::decreaseLevel(level_t target) {
        while (clevel > target) {
            unselectLevel();
            solver_contrads.pop();
            solver_consistency.pop();
            --clevel;
        }
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::selectCurrentLiteral() {
        addSolverLiteral(getCurrentIndex());
        hypothesis.addLiteral(getCurrentIndex(), clevel);
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::addSolverLiteral(index_t idx) {
        solver_contrads.addLiteral(getLiteral(idx));
        solver_consistency.addLiteral(getLiteral(idx));
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::clearSolversCurrentLevel() {
        solver_contrads.pop();
        solver_contrads.push();
        solver_consistency.pop();
        solver_consistency.push();
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::unselectLevel() {
        hypothesis.removeLiterals(clevel);
        clearSolversCurrentLevel();
    }

    template<typename InterfaceT>
    inline bool NaiveAbducibleEngine<InterfaceT>::isConsistent(LiteralReference h) {
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
    inline bool NaiveAbducibleEngine<InterfaceT>::canBeSkipped(LiteralReference h) {
        if (skipctrl.max_level <= clevel) {
            skip_counters.level_depth++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":depth"),
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
    inline void NaiveAbducibleEngine<InterfaceT>::backtrack(level_t level) {
        accessLevel(level);
        clearSolversCurrentLevel();
    }

    template<typename InterfaceT>
    inline bool NaiveAbducibleEngine<InterfaceT>::isUnselected(index_t idx, level_t lvl) {
        for (level_t l = 0; l < lvl; l++) {
            if (selection_map[l] == idx) {
                return false;
            }
        }
        return true;
    }

    template<typename InterfaceT>
    inline bool NaiveAbducibleEngine<InterfaceT>::searchNextLiteral(level_t level) {
        accessLevel(level);
        unselectLevel();
        while (++selection_map[clevel] < msize) {
            if (isUnselected(selection_map[clevel], clevel)) {
                return true;
            }
        }
        return false;
    }

    template<typename InterfaceT>
    inline typename InterfaceT::LiteralT&
    NaiveAbducibleEngine<InterfaceT>::getLiteral(index_t idx) {
        return lmapper.get(idx);
    }

    template<typename InterfaceT>
    inline typename NaiveAbducibleEngine<InterfaceT>::index_t
    NaiveAbducibleEngine<InterfaceT>::getCurrentIndex() {
        return selection_map[clevel];
    }

    template<typename InterfaceT>
    inline typename InterfaceT::LiteralT&
    NaiveAbducibleEngine<InterfaceT>::getCurrentLiteral() {
        return getLiteral(getCurrentIndex());
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::modelCleanUp() {
        snlog::l_internal("Models not available in naive engine");
    }

    template<typename InterfaceT>
    inline void NaiveAbducibleEngine<InterfaceT>::storeCurrentImplicate() {
        snlog::l_internal("Storage not available in naive engine");
    }

    template<typename InterfaceT>
    inline SolverTestStatus NaiveAbducibleEngine<InterfaceT>::testHypothesis(level_t level) {
        accessLevel(level);
        insthandle(instrument::idata(solver_consistency.getPrintableAssertions(false)),
                   instrument::instloc::ismt_test);
        SolverTestStatus status = solver_contrads.check();
        insthandle(instrument::idata(to_string(status)), instrument::instloc::ismt_result);
        return status;
    }

}

#endif
