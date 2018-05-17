/**
 * \file gpid/util/storage.hpp
 * \brief Implicate storage template algorithms
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__UTIL__STORAGE_HPP
#define GPID_FRAMEWORK__UTIL__STORAGE_HPP

#include <map>
#include <set>

#include <snlog/snlog.hpp>
#include <dot/dotgraph.hpp>

#include <gpid/core/solvers.hpp>
#include <gpid/util/stdutils.hpp>

namespace gpid {

    template<class ATUtils>
    class AbducibleTree {

        typedef uint32_t mapindex_t;
        mapindex_t _cbound = 1;

        ATUtils utils;
        typename ATUtils::SolverT subsumptionSolver;
        typename ATUtils::SolverT insertionSolver;

        std::map<mapindex_t, std::map<typename ATUtils::LiteralT, mapindex_t>> nodes;
        std::set<mapindex_t> tnodes;
        typename ATUtils::FormulaT formula;

        inline mapindex_t newNode() { return ++_cbound; }

        inline void printLocal(mapindex_t idx, typename ATUtils::FormulaT cformula);
        inline void cleanSubsumedLocal(mapindex_t idx);

        inline void insertLocal(mapindex_t idx, const typename ATUtils::LiteralListT& impset,
                                uint32_t impset_pos, bool negate);
        inline bool containsLocal(mapindex_t idx, const typename ATUtils::LiteralListT& impset,
                                  uint32_t impset_pos, bool negate);

        inline int buildGraphLocal(mapindex_t idx, dot::Graph& g);
    public:

        template<class ... ATUtilsInitializers>
        AbducibleTree(ATUtilsInitializers& ... its)
            : utils(its...), subsumptionSolver(its...), insertionSolver(its...), formula(its...)
        { subsumptionSolver.push(); }

        inline void print();
        inline bool subsumes(typename ATUtils::FormulaT implicate, bool negate=true);
        inline void cleanSubsumed(typename ATUtils::FormulaT sourcef, bool negate=true);
        inline void insert(const typename ATUtils::LiteralListT& impset, bool negate=true);
        inline bool contains(const typename ATUtils::LiteralListT& impset, bool negate=true);
        inline void exportGraph(std::ostream& target);
    };



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

}

#endif
