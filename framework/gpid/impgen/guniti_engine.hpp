/**
 * \file gpid/impgen/guniti_engine.hpp
 * \brief GPiD-Framework Guniti Engine for Unit Implicate Generation.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__IMPGEN__GUNITI_ENGINE_HPP
#define GPID_FRAMEWORK__IMPGEN__GUNITI_ENGINE_HPP

#include <list>
#include <fstream>

#include <gpid/core/memory.hpp>
#include <gpid/core/saitypes.hpp>
#include <gpid/storage/atrees.hpp>
#include <gpid/impgen/skipcontrol.hpp>
#include <gpid/instrument/instrument.hpp>

namespace gpid {

    class GunitiHypothesis {
    public:
        typedef uint32_t index_t;
    private:
        index_t lit;
    public:
        template <typename T> class giterator {
            index_t value;
            bool read;
        public:
            giterator() : value(0), read(true) {}
            giterator(index_t value) : value(value), read(false) {}
            inline bool operator!=(const giterator<T>& o) const
            { return read != o.read; }
            inline bool operator==(const giterator<T>& o) const
            { return read == o.read; }
            inline giterator& operator++()
            { read = true; return *this; }
            inline       T operator*()       { return value; }
            inline const T operator*() const { return value; }
        };
        using iterator = giterator<index_t>;
        using const_iterator = giterator<const index_t>;
        inline iterator begin() { return iterator(lit); }
        inline iterator end() { return iterator(); }
        inline const_iterator cbegin() { return const_iterator(lit); }
        inline const_iterator cend() { return const_iterator(); }

        GunitiHypothesis(index_t lit) : lit(lit) {}

        inline void addLiteral(index_t l, uint32_t) { lit = l; } // Wrapper
        inline void removeLiterals(uint32_t) { lit = 0; } // Wrapper
    };

    /** \brief Class for handling abducible literals. \ingroup gpidcorelib */
    template<class InterfaceT>
    class GunitiEngine {
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
    private:
        SolverInterfaceEngine<InterfaceT> interfaceEngine;
        InterfaceT& solver_contrads;

        starray::StaticActivableArray lactive;
        ObjectMapper<LiteralT> lmapper;
        using LiteralReference = typename ObjectMapper<LiteralT>::index_t;

        AbducibleTree<InterfaceT, GunitiHypothesis> storage;
        index_t selection;

        SkipController skipctrl;
        struct {
            counter_t storage = 0;
        } skip_counters;

        std::map<std::string, counter_t> counts_wrap;

        inline void addSolverLiteral(index_t idx);
        inline void clearSolversLiteral();

        /** \brief Decide if an literal can be skipped at a given level. */
        inline bool canBeSkipped(LiteralReference h);

        inline LiteralT& getLiteral(index_t idx);
        inline index_t getCurrentIndex();
    public:
        /** Create an abducible engine. */
        GunitiEngine(size_t size, ContextManagerT& ctx, GunitiOptions& iopts);
        /** Create an abducible engine. */
        template<typename AbducibleSource>
        GunitiEngine(AbducibleSource& source, ContextManagerT& ctx, GunitiOptions& iopts);

        /** Reinitialize the abducible engine. */
        inline void reinit();
        /** Initialize the underlying solver interface with a given problem. */
        inline void initializeSolvers(ProblemLoaderT& pbld);

        /** Map an index of the set to a specific literal. */
        inline void mapLiteral(uint32_t idx, LiteralT* hyp);

        /** Original size of the set. */
        inline uint32_t getSourceSize();
        /** Count of skipped candidates for various reasons. */
        inline std::map<std::string, counter_t>& getSkippedCounts();

        /** Check if the current hypothesis is a contradiction to the problem. */
        inline SolverTestStatus testEmpty();
        inline SolverTestStatus testCurrentLiteral();

        /** Print the current hypothesis in implicate format. */
        inline void printCurrentImplicate();
        /** Print the current implicate storage structure state. */
        inline void printStorage();
        /** Export the current implicate storage structure state. */
        inline void exportStorage(const std::string filename);

        /**
         * \brief Find the next non tested literal.
         * \return true iff there exists a valid non-tested literal at depth level.
         *
         * If such an literal exists, this method will also position the
         * internal literal pointer on it, allowing the selected literal
         * to be accessed/recovered via the \ref getCurrentLiteral method.
         */
        inline bool selectNextLiteral();
        /** Recover the current literal. */
        inline LiteralT& getCurrentLiteral();

        /** Internally selects literals to skip according to a model. */
        inline void modelCleanUp();

        inline void prepruneInconsistentLiterals();

        /** Insert the current hypothsis as an implicate in the storage structure. */
        inline void storeCurrentImplicate();
    };

    /* *** Implementations *** */

    template<typename InterfaceT> GunitiEngine<InterfaceT>::GunitiEngine
    (size_t size, ContextManagerT& ctx, GunitiOptions& iopts)
        : interfaceEngine(ctx),
          solver_contrads(interfaceEngine.newInterface()),
          lactive(size),
          storage(interfaceEngine.newInterface(), lmapper),
          skipctrl(iopts)
    {
        reinit();
        solver_contrads.push();
    }

    template<typename InterfaceT>
    template<typename AbducibleSource> GunitiEngine<InterfaceT>::GunitiEngine
    (AbducibleSource& source, ContextManagerT& ctx, GunitiOptions& iopts)
        : interfaceEngine(ctx),
          solver_contrads(interfaceEngine.newInterface()),
          lactive(source.count()),
          lmapper(source.getMapper()),
          storage(interfaceEngine.newInterface(), lmapper),
          skipctrl(iopts)
    {
        reinit();
        solver_contrads.push();
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::reinit() {
        lactive.activate_all();
        selection = lactive.get_first();
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::initializeSolvers(ProblemLoaderT& pbld) {
        pbld.prepareReader();
        solver_contrads.pop();
        while (pbld.hasConstraint()) {
            solver_contrads.addConstraint(pbld.nextConstraint());
        }
        solver_contrads.push();
    }

    template<typename InterfaceT>
    inline uint32_t GunitiEngine<InterfaceT>::getSourceSize() {
        return lactive.get_maximal_size();
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::mapLiteral(index_t idx, LiteralT* hyp) {
        lmapper.map(idx, hyp);
    }

    template<typename InterfaceT>
    inline std::map<std::string, uint64_t>& GunitiEngine<InterfaceT>::getSkippedCounts() {
        counts_wrap["storage"] = skip_counters.storage;
        return counts_wrap;
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::printCurrentImplicate() {
        GunitiHypothesis hyp(getCurrentIndex());
        printlh(implicate<InterfaceT>(hyp, lmapper, interfaceEngine.getContextManager()));
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::printStorage() {
        storage.print();
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::exportStorage(const std::string filename) {
        std::ofstream outstr(filename);
        storage.exportGraph(outstr);
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::addSolverLiteral(index_t idx) {
        solver_contrads.addLiteral(getLiteral(idx));
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::clearSolversLiteral() {
        solver_contrads.pop();
        solver_contrads.push();
    }

    template<typename InterfaceT>
    inline bool GunitiEngine<InterfaceT>::canBeSkipped(LiteralReference h) {
        GunitiHypothesis hyp(getCurrentIndex());
        if (skipctrl.storage && storage.fwdSubsumes(hyp, h)) {
            skip_counters.storage++;
            insthandle(instrument::idata(lmapper.get(h).str() + ":storage"),
                       instrument::instloc::skip);
            return true;
        }
        return false;
    }

    template<typename InterfaceT>
    inline bool GunitiEngine<InterfaceT>::selectNextLiteral() {
        while (true) {
            if (lactive.has_next()) {
                selection = lactive.get_next();
                insthandle(instrument::idata(getCurrentLiteral().str()),
                           instrument::instloc::pre_select);
                if (!canBeSkipped(getCurrentIndex())) {
                    clearSolversLiteral();
                    addSolverLiteral(getCurrentIndex());
                    return true;
                }
            } else {
                return false;
            }
        }
    }

    template<typename InterfaceT>
    inline typename InterfaceT::LiteralT&
    GunitiEngine<InterfaceT>::getLiteral(index_t idx) {
        return lmapper.get(idx);
    }

    template<typename InterfaceT>
    inline typename GunitiEngine<InterfaceT>::index_t
    GunitiEngine<InterfaceT>::getCurrentIndex() {
        return selection;
    }

    template<typename InterfaceT>
    inline typename InterfaceT::LiteralT&
    GunitiEngine<InterfaceT>::getCurrentLiteral() {
        return getLiteral(getCurrentIndex());
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::modelCleanUp() {
        const ModelT& model = solver_contrads.getModel();
        for (index_t idx = 0; idx <= lactive.get_last(); ++idx) {
            if (!lactive.is_active(idx)) continue;
            if (model.implies(getLiteral(idx))) {
                lactive.deactivate(idx);
                insthandle(instrument::idata(getLiteral(idx).str() + ":model"),
                           instrument::instloc::skip);
            }
        }
        lactive.reset_iterator();
        selection = lactive.get_first();
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::prepruneInconsistentLiterals() {
        InterfaceT& solver_tmp = interfaceEngine.newInterface();
        for (index_t idx = 0; idx <= lactive.get_last(); ++idx) {
            if (!lactive.is_active(idx)) continue;
            solver_tmp.push();
            solver_tmp.addLiteral(getLiteral(idx));
            SolverTestStatus status = solver_tmp.check();
            if (status == SolverTestStatus::UNSAT) {
                snlog::l_info() << "Inconsistent literal : " << getLiteral(idx).str()
                                << " -- removed" << snlog::l_end;
                lactive.deactivate(idx);
            } else if (status == SolverTestStatus::UNKNOWN) {
                snlog::l_warn() << "Interface-undecidable literal detected: "
                                << getLiteral(idx).str() << snlog::l_end;
            }
            solver_tmp.pop();
        }
        lactive.reset_iterator();
        selection = lactive.get_first();
    }

    template<typename InterfaceT>
    inline void GunitiEngine<InterfaceT>::storeCurrentImplicate() {
        GunitiHypothesis hyp(getCurrentIndex());
        storage.bwdSubsumesRemove(hyp);
        storage.insert(hyp);
    }

    template<typename InterfaceT>
    inline SolverTestStatus GunitiEngine<InterfaceT>::testEmpty() {
        insthandle(instrument::idata("empty"), instrument::instloc::ismt_test);
        SolverTestStatus status = solver_contrads.check();
        insthandle(instrument::idata(to_string(status)), instrument::instloc::ismt_result);
        return status;
    }

    template<typename InterfaceT>
    inline SolverTestStatus GunitiEngine<InterfaceT>::testCurrentLiteral() {
        insthandle(instrument::idata(solver_contrads.getPrintableAssertions(false)),
                   instrument::instloc::ismt_test);
        SolverTestStatus status = solver_contrads.check();
        insthandle(instrument::idata(to_string(status)), instrument::instloc::ismt_result);
        return status;
    }

}

#endif
