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
        std::set<anidx_t> tnodes;

        typedef LiteralHypothesis<typename SolverT::LiteralT> HypothesisT;

        inline void insertLocal(anidx_t idx, HypothesisT& h, typename HypothesisT::iterator& it);
        inline bool containsLocal(anidx_t idx, HypothesisT& h, typename HypothesisT::iterator& it);

        inline bool fwdSubsumesLocal(anidx_t idx);
        inline void bwdSubsumesRemoveLocal(anidx_t idx);

        inline void printLocal(anidx_t idx, HypothesisT& cprint, uint32_t clvl);
        inline int buildGraphLocal(anidx_t idx, dot::Graph& g);

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
            tnodes.insert(idx);
            return;
        }
        LiteralRefT l_loc = *it;
        if (gmisc::ninmap(nodes[idx], l_loc))
            nodes[idx][l_loc] = newNidx();
        insertLocal(nodes[idx][l_loc], h, ++it);
    }

    template<class ATUtils>
    inline bool AbducibleTree<ATUtils>::contains(HypothesisT& h)
    { typename HypothesisT::iterator it = h.begin(); return containsLocal(1, h, it); }

    template<class ATUtils>
    inline bool AbducibleTree<ATUtils>::containsLocal(anidx_t idx, HypothesisT& h,
                                                      typename HypothesisT::iterator& it) {
        if (it == h.end()) {
            return gmisc::inset(tnodes, idx);
        }
        LiteralRefT l_loc = *it;
        return gmisc::inmap(nodes[idx], l_loc) ?
            containsLocal(nodes[idx][l_loc], h, ++it) : false;
    }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::bwdSubsumesRemove(HypothesisT& h) {
        solver.push();
        solver.addClause(h, mapper, true);
        bwdSubsumesRemoveLocal(1);
        solver.pop();
    }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::bwdSubsumesRemoveLocal(anidx_t idx) {
        if (nodes[idx].empty()) return;
        SolverTestStatus res = solver.check();
        if (res == SolverTestStatus::UNKNOWN) {
            snlog::l_error("Storage insertion satisfiability test returned unknown");
        }
        if (res == SolverTestStatus::SAT) {
            for (auto p : nodes[idx]) {
                solver.push();
                solver.addLiteral(mapper.get(p.first));
                bwdSubsumesRemoveLocal(p.second);
                solver.pop();
            }
        } else {
            nodes[idx].clear();
        }
    }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::print() {
        HypothesisT printable(mapper.size());
        printLocal(1, printable, 1);
    }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::printLocal(anidx_t idx, HypothesisT& cprint, uint32_t clvl) {
        if (nodes[idx].empty() && gmisc::inset(tnodes, idx)) {
            print_item(implicate(cprint, mapper));
        } else {
            for (auto p : nodes[idx]) {
                cprint.addLiteral(p.first, clvl);
                printLocal(p.second, cprint, clvl+1);
                cprint.removeLiterals(clvl);
            }
        }
    }

    template<class SolverT>
    inline void AbducibleTree<SolverT>::exportGraph(std::ostream& target) {
        dot::Graph g("AbducibleStorageTree");
        buildGraphLocal(1, g);
        target << g;
    }

    template<class SolverT>
    inline int AbducibleTree<SolverT>::buildGraphLocal(anidx_t idx, dot::Graph& g) {
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
                snlog::l_warn("Not Correctly Printed: storage::buildGraphLocal literal edge format");
                snlog::l_info("Currently prints mapping index and not content");
                g.createEdge(loc, child, std::to_string(p.first), dot::types::ClassicEdge);
            }
            return loc;
        }
    }

    template<class SolverT>
    inline bool AbducibleTree<SolverT>::fwdSubsumes(HypothesisT& h, LiteralRefT l_add) {
        solver.push();
        solver.addLiteral(mapper.get(l_add));
        bool res = fwdSubsumes(h);
        solver.pop();
        return res;
    }

    template<class SolverT>
    inline bool AbducibleTree<SolverT>::fwdSubsumes(HypothesisT& h) {
        solver.push();
        for (anidx_t hl : h) {
            solver.addLiteral(mapper.get(hl));
        }
        bool res = fwdSubsumesLocal(1);
        solver.pop();
        return res;
    }

    template<class SolverT>
    inline bool AbducibleTree<SolverT>::fwdSubsumesLocal(anidx_t idx) {
        for (auto p : nodes[idx]) {
            solver.push();
            solver.addLiteral(mapper.get(p.first), true);
            SolverTestStatus res = solver.check();
            if (res == SolverTestStatus::UNKNOWN) {
                snlog::l_error("Storage insertion satisfiability test returned unknown");
            }
            if (res == SolverTestStatus::UNSAT) {
                if (fwdSubsumesLocal(p.second)) {
                    return true;
                }
            }
            solver.pop();
        }
        return false;
    }

}

#endif
