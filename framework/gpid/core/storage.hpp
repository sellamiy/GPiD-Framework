/**
 * \file gpid/util/storage.hpp
 * \brief Implicate storage template algorithms
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__UTIL__STORAGE_HPP
#define GPID_FRAMEWORK__UTIL__STORAGE_HPP

#include <limits>

#include <dot/dotgraph.hpp>

#include <gpid/core/wrappers.hpp>
#include <gpid/util/stdutils.hpp>

namespace gpid {

    template<class SolverT>
    class AbducibleTree {

        typedef uint32_t anidx_t;
        anidx_t _nbound = 1;
        inline anidx_t newNidx() { return ++_nbound; }

        typename SolverT::InterfaceT& solver;
        LiteralMapper<typename SolverT::LiteralT>& mapper;

        typedef typename LiteralMapper<typename SolverT::LiteralT>::index_t LiteralRefT;
        std::map<anidx_t, std::map<LiteralRefT, anidx_t>> nodes;
        std::set<anidx_t> _tnodes;

        typedef LiteralHypothesis<typename SolverT::LiteralT> HypothesisT;

        inline void insertLocal(anidx_t idx, HypothesisT& h, typename HypothesisT::iterator& it);
        inline bool containsLocal(anidx_t idx);

        inline void fwdSubsumesLocal(anidx_t idx);
        inline void bwdSubsumesRemoveLocal(anidx_t idx);

        inline void printLocal(anidx_t idx);
        inline int buildGraphLocal(anidx_t idx);

    public:

        AbducibleTree(SolverT& solver, LiteralMapper<typename SolverT::LiteralT>& mapper)
            : solver(solver.additionalInterface()), mapper(mapper) { }

        inline void insert(HypothesisT& h);
        inline bool contains(HypothesisT& h);

        inline bool fwdSubsumes(HypothesisT& h);
        inline bool fwdSubsumes(HypothesisT& h, LiteralRefT l_add);
        inline void bwdSubsumesRemove(HypothesisT& h);

        inline void print();
        inline void exportGraph(std::ostream& target);

    };

    template<class SolverT>
    inline void AbducibleTree<SolverT>::insert(HypothesisT& h)
    { typename HypothesisT::iterator it = h.begin(); insertLocal(1, h, it); }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::insertLocal(anidx_t idx, HypothesisT& h,
                                                    typename HypothesisT::iterator& it) {
        if (it == h.end()) {
            _tnodes.insert(idx);
            return;
        }
        LiteralRefT l_loc = *it;
        if (gmisc::ninmap(nodes[idx], l_loc))
            nodes[idx][l_loc] = newNidx();
        insertLocal(nodes[idx][l_loc], h, ++it);
    }

    /* * UNCOMPLETE * */

    template<class SolverT>
    inline void AbducibleTree<SolverT>::bwdSubsumesRemove(HypothesisT&)
    { snlog::l_warn("Not Implemented Yet: storage::backwardSubsumption"); }

    template<class SolverT>
    inline bool AbducibleTree<SolverT>::fwdSubsumes(HypothesisT& h, LiteralRefT l_add) {
        h.addLiteral(l_add, std::numeric_limits<uint32_t>::max());
        bool res = fwdSubsumes(h);
        h.removeLiterals(std::numeric_limits<uint32_t>::max());
        return res;
    }

    template<class SolverT>
    inline bool AbducibleTree<SolverT>::fwdSubsumes(HypothesisT&)
    { snlog::l_warn("Not Implemented Yet: storage::fwdSubsumes"); return false; }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::print()
    { snlog::l_warn("Not Implemented Yet: storage::print"); }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::exportGraph(std::ostream&)
    { snlog::l_warn("Not Implemented Yet: storage::exportGraph"); }

    /*
    template<class ATUtils>
    inline void AbducibleTree<ATUtils>::print() { printLocal(1, utils.emptyFormula()); }

    template<class ATUtils>
    inline void AbducibleTree<ATUtils>::printLocal(mapindex_t idx, typename ATUtils::FormulaT cformula) {
        if (nodes[idx].empty() && gmisc::inset(tnodes, idx)) {
            utils.printImplicate(cformula);
        } else {
            for (auto p : nodes[idx]) {
                printLocal(p.second, utils.disjunction(cformula, utils.toFormula(p.first)));
            }
        }
    }

    template<class ATUtils>
    inline bool AbducibleTree<ATUtils>::subsumes(typename ATUtils::FormulaT implicate, bool negate) {
        subsumptionSolver.push();
        subsumptionSolver.addFormula(implicate, negate);
        SolverTestStatus res = subsumptionSolver.check();
        subsumptionSolver.pop();
        if (res == SOLVER_UNKNOWN) {
            snlog::l_error("Subsumption satisfiability test returned unknown");
        }
        return res == SOLVER_UNSAT;
    }

    template<class ATUtils>
    inline void AbducibleTree<ATUtils>::cleanSubsumed(typename ATUtils::FormulaT sourcef, bool negate) {
        insertionSolver.push();
        insertionSolver.addFormula(sourcef, negate);
        cleanSubsumedLocal(1);
        insertionSolver.pop();
    }

    template<class ATUtils>
    inline void AbducibleTree<ATUtils>::cleanSubsumedLocal(mapindex_t idx) {
        if (nodes[idx].empty()) return;
        SolverTestStatus res = insertionSolver.check();
        if (res == SOLVER_UNKNOWN) {
            snlog::l_error("Storage insertion satisfiability test returned unknown");
        }
        if (res == SOLVER_SAT) {
            for (auto p : nodes[idx]) {
                insertionSolver.push();
                insertionSolver.addFormula(utils.toFormula(p.first), true);
                cleanSubsumedLocal(p.second);
                insertionSolver.pop();
            }
        } else {
            nodes[idx].clear();
        }
    }

    template<class ATUtils>
    inline void AbducibleTree<ATUtils>::insert(const typename ATUtils::LiteralListT& impset, bool negate) {
        insertLocal(1, impset, 0, negate);
        subsumptionSolver.pop();
        subsumptionSolver.push();
        formula = utils.disjunction(formula, utils.toFormula(impset, negate));
        subsumptionSolver.addFormula(formula, false);
    }

    template<class ATUtils>
    inline void AbducibleTree<ATUtils>::insertLocal(mapindex_t idx,
                                                    const typename ATUtils::LiteralListT& impset,
                                                    uint32_t impset_pos, bool negate) {
        if (impset_pos == impset.size()) {
            tnodes.insert(idx);
            return;
        }
        typename ATUtils::LiteralT lit = negate ?
            utils.negation(impset[impset_pos]) : impset[impset_pos];
        if (gmisc::ninmap(nodes[idx], lit))
            nodes[idx][lit] = newNode();
        insertLocal(nodes[idx][lit], impset, impset_pos + 1, negate);
    }

    template<class ATUtils>
    inline bool AbducibleTree<ATUtils>::contains(const typename ATUtils::LiteralListT& impset, bool negate)
    { return containsLocal(1, impset, 0, negate); }

    template<class ATUtils>
    inline bool AbducibleTree<ATUtils>::containsLocal(mapindex_t idx,
                                                      const typename ATUtils::LiteralListT& impset,
                                                      uint32_t impset_pos, bool negate) {
        if (impset_pos == impset.size()) {
            return gmisc::inset(tnodes, idx);
        }
        typename ATUtils::LiteralT lit = negate ?
            utils.negation(impset[impset_pos]) : impset[impset_pos];
        return gmisc::inmap(nodes[idx], lit) ?
            containsLocal(nodes[idx][lit], impset, impset_pos + 1, negate)
            : false;
    }

    template<class ATUtils>
    inline void AbducibleTree<ATUtils>::exportGraph(std::ostream& target) {
        dot::Graph g("AbdStorage");
        buildGraphLocal(1, g);
        target << g;
    }

    template<class ATUtils>
    inline int AbducibleTree<ATUtils>::buildGraphLocal(mapindex_t idx, dot::Graph& g) {
        if (nodes[idx].empty()) {
            if (gmisc::inset(tnodes, idx)) {
                return g.createNode(std::to_string(idx), dot::types::GreenDiamondNode);
            } else {
                return g.createNode(std::to_string(idx), dot::types::RedDiamondNode);
            }
        } else {
            int loc, child;
            loc = g.createNode(std::to_string(idx), dot::types::ClassicDiamondNode);
            for (auto p : nodes[idx]) {
                child = buildGraphLocal(p.second, g);
                g.createEdge(loc, child, utils.toString(p.first), dot::types::ClassicEdge);
            }
            return loc;
        }
    }
    */

}

#endif
