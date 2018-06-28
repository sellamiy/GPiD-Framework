/**
 * \file gpid/storage/atrees.hpp
 * \brief Implicate storage template algorithms
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__STORAGE__ATREES_HPP
#define GPID_FRAMEWORK__STORAGE__ATREES_HPP

#include <lcdot/dotgraph.hpp>

#include <gpid/core/literals.hpp>
#include <gpid/utils/stdutils.hpp>

namespace gpid {

    template<typename InterfaceT, typename HypothesisT>
    class AbducibleTree {

        using anidx_t = uint32_t;
        anidx_t _nbound = 1;
        inline anidx_t newNidx() { return ++_nbound; }

        InterfaceT& solver;
        ObjectMapper<typename InterfaceT::LiteralT>& mapper;

        using LiteralRefT = typename ObjectMapper<typename InterfaceT::LiteralT>::index_t;
        std::map<anidx_t, std::map<LiteralRefT, anidx_t>> nodes;
        std::set<anidx_t> tnodes;

        inline void insertLocal(anidx_t idx, HypothesisT& h, typename HypothesisT::iterator& it);
        inline bool containsLocal(anidx_t idx, HypothesisT& h, typename HypothesisT::iterator& it);

        inline bool fwdSubsumesLocal(anidx_t idx);
        inline void bwdSubsumesRemoveLocal(anidx_t idx);

        inline void printLocal(anidx_t idx, HypothesisT& cprint, uint32_t clvl);
        inline int buildGraphLocal(anidx_t idx, lcdot::Graph& g);

    public:

        AbducibleTree(InterfaceT& solver, ObjectMapper<typename InterfaceT::LiteralT>& mapper)
            : solver(solver), mapper(mapper) { }

        inline void insert(HypothesisT& h);
        inline bool contains(HypothesisT& h);

        inline bool fwdSubsumes(HypothesisT& h);
        inline bool fwdSubsumes(HypothesisT& h, LiteralRefT l_add);
        inline void bwdSubsumesRemove(HypothesisT& h);

        inline void print();
        inline void exportGraph(std::ostream& target);

    };

    template<typename InterfaceT, typename HypothesisT>
    inline void AbducibleTree<InterfaceT, HypothesisT>::insert(HypothesisT& h)
    { typename HypothesisT::iterator it = h.begin(); insertLocal(1, h, it); }

    template<typename InterfaceT, typename HypothesisT>
    inline void
    AbducibleTree<InterfaceT, HypothesisT>::insertLocal(anidx_t idx, HypothesisT& h,
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

    template<typename InterfaceT, typename HypothesisT>
    inline bool AbducibleTree<InterfaceT, HypothesisT>::contains(HypothesisT& h)
    { typename HypothesisT::iterator it = h.begin(); return containsLocal(1, h, it); }

    template<typename InterfaceT, typename HypothesisT>
    inline bool
    AbducibleTree<InterfaceT, HypothesisT>::containsLocal(anidx_t idx, HypothesisT& h,
                                                          typename HypothesisT::iterator& it) {
        if (it == h.end()) {
            return gmisc::inset(tnodes, idx);
        }
        LiteralRefT l_loc = *it;
        return gmisc::inmap(nodes[idx], l_loc) ?
            containsLocal(nodes[idx][l_loc], h, ++it) : false;
    }

    template<typename InterfaceT, typename HypothesisT>
    inline void AbducibleTree<InterfaceT, HypothesisT>::bwdSubsumesRemove(HypothesisT& h) {
        solver.push();
        solver.addClause(h, mapper, true);
        bwdSubsumesRemoveLocal(1);
        /* TODO: Obtain a better way to write the Minisat interface
           API. Adding a specific method for it in a global framework
           is not a good one. */
        solver.clearUnsafeClauses();
        solver.pop();
    }

    template<typename InterfaceT, typename HypothesisT>
    inline void AbducibleTree<InterfaceT, HypothesisT>::bwdSubsumesRemoveLocal(anidx_t idx) {
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

    template<typename InterfaceT, typename HypothesisT>
    inline void AbducibleTree<InterfaceT, HypothesisT>::print() {
        HypothesisT printable(mapper.size());
        printLocal(1, printable, 1);
    }

    template<typename InterfaceT, typename HypothesisT>
    inline void AbducibleTree<InterfaceT, HypothesisT>::printLocal(anidx_t idx, HypothesisT& cprint,
                                                                   uint32_t clvl) {
        if (nodes[idx].empty() && gmisc::inset(tnodes, idx)) {
            printlh(implicate<InterfaceT>(cprint, mapper));
        } else {
            for (auto p : nodes[idx]) {
                cprint.addLiteral(p.first, clvl);
                printLocal(p.second, cprint, clvl+1);
                cprint.removeLiterals(clvl);
            }
        }
    }

    template<typename InterfaceT, typename HypothesisT>
    inline void AbducibleTree<InterfaceT, HypothesisT>::exportGraph(std::ostream& target) {
        lcdot::Graph g("AbducibleStorageTree");
        buildGraphLocal(1, g);
        target << g;
    }

    template<typename InterfaceT, typename HypothesisT>
    inline int AbducibleTree<InterfaceT, HypothesisT>::buildGraphLocal(anidx_t idx, lcdot::Graph& g) {
        if (nodes[idx].empty()) {
            if (gmisc::inset(tnodes, idx)) {
                return g.createNode(std::to_string(idx), lcdot::types::GreenDiamondNode);
            } else {
                return g.createNode(std::to_string(idx), lcdot::types::RedDiamondNode);
            }
        } else {
            int loc, child;
            loc = g.createNode(std::to_string(idx), lcdot::types::ClassicDiamondNode);
            for (auto p : nodes[idx]) {
                child = buildGraphLocal(p.second, g);
                // TODO: Edge printer system still anchored in old printing structure
                g.createEdge(loc, child, mapper.get(p.first).str(), lcdot::types::ClassicEdge);
            }
            return loc;
        }
    }

    template<typename InterfaceT, typename HypothesisT>
    inline bool AbducibleTree<InterfaceT, HypothesisT>::fwdSubsumes(HypothesisT& h, LiteralRefT l_add) {
        solver.push();
        solver.addLiteral(mapper.get(l_add));
        bool res = fwdSubsumes(h);
        solver.pop();
        return res;
    }

    template<typename InterfaceT, typename HypothesisT>
    inline bool AbducibleTree<InterfaceT, HypothesisT>::fwdSubsumes(HypothesisT& h) {
        solver.push();
        for (anidx_t hl : h) {
            solver.addLiteral(mapper.get(hl));
        }
        bool res = fwdSubsumesLocal(1);
        solver.pop();
        return res;
    }

    template<typename InterfaceT, typename HypothesisT>
    inline bool AbducibleTree<InterfaceT, HypothesisT>::fwdSubsumesLocal(anidx_t idx) {
        if (nodes[idx].empty()) {
            return gmisc::inset(tnodes, idx);
        }
        for (auto p : nodes[idx]) {
            solver.push();
            solver.addLiteral(mapper.get(p.first), true);
            SolverTestStatus res = solver.check();
            solver.pop();
            if (res == SolverTestStatus::UNKNOWN) {
                snlog::l_error("Storage insertion satisfiability test returned unknown");
            }
            if (res == SolverTestStatus::UNSAT) {
                if (fwdSubsumesLocal(p.second)) {
                    return true;
                }
            }
        }
        return false;
    }

}

#endif
