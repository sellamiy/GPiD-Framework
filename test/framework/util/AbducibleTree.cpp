#include <vector>
#include <gtest/gtest.h>
#include <gpid/gpid.hpp>
#include <gpid/util/storage.hpp>

#define ABDUCIBLE_TREE_TEST

#warning To Update

using namespace gpid;
/*
struct ATAutoIntWr {
    uint32_t v;
    ATAutoIntWr() : v(0) {}
    ATAutoIntWr(const ATAutoIntWr& o) : v(o.v) {}
    ATAutoIntWr(const uint32_t u) : v(u) {}
    bool operator < (const ATAutoIntWr& o) const { return v < o.v; }
};

struct ATAutoIntListWr {
    std::vector<uint32_t> l;
    ATAutoIntListWr() {}
    ATAutoIntListWr(const ATAutoIntListWr& o) : l(o.l) {}
    ATAutoIntListWr(const std::vector<uint32_t>& ol) : l(ol) {}
    unsigned int size() const { return l.size(); }
    ATAutoIntWr operator[] (const int index) const { return ATAutoIntWr(l[index]); };
};

static bool findin(ATAutoIntListWr s, uint32_t i) {
    for (auto j : s.l) {
        if (i == j) return true;
    }
    return false;
}

static bool subsets(ATAutoIntListWr s, ATAutoIntListWr t) {
    for (auto i : s.l) {
        if (!findin(t, i)) return false;
    }
    return true;
}

struct ATSolverZero {

    unsigned int _lvl = 0;
    std::vector<unsigned int> _lvs;
    std::vector<ATAutoIntListWr> _data;

    void addFormula(ATAutoIntListWr f, bool) { _data.push_back(f); }

    void push() { _lvs.push_back(_data.size()); }

    void pop() { _lvl = _lvs.back(); _lvs.pop_back(); while(_data.size() > _lvl) _data.pop_back(); }

};

struct ATAutoSolver : public ATSolverZero {

    SolverTestStatus check() {
        for (unsigned int i=0; i < _lvs.back(); ++i) {
            if (subsets(_data[i], _data.back())) return SOLVER_UNSAT;
        }
        return SOLVER_SAT;
    }

};

struct ATRevoSolver : public ATSolverZero {

    SolverTestStatus check() {
        std::vector<unsigned int> _ndata;
        for (unsigned int i=1; i < _data.size(); ++i) _ndata.push_back(_data[i][0].v);
        if (subsets(_data[0], ATAutoIntListWr(_ndata))) return SOLVER_UNSAT;
        return SOLVER_SAT;
    }

};

struct ATTUtils0 {
    typedef ATAutoIntWr LiteralT;
    typedef ATAutoIntListWr LiteralListT;
    typedef ATAutoIntListWr FormulaT;

    LiteralT negation(LiteralT l) const { return l; }
    FormulaT negation(FormulaT f) const { return f; }
    FormulaT disjunction(FormulaT l, FormulaT r) const
    { for (auto i : r.l) l.l.push_back(i); return l; }
    FormulaT toFormula(LiteralListT ll, bool) const { return ll; }
    FormulaT toFormula(LiteralT l) const { return FormulaT({l.v}); }
};

struct ATTUtils_x101 : public ATTUtils0 {
    typedef ATAutoSolver SolverT;
};

struct ATTUtils_x102 : public ATTUtils0 {
    typedef ATRevoSolver SolverT;
};

class SubsumerBasic_101c : public ::testing::Test {
protected:

    AbducibleTree<ATTUtils_x101> *tree;

    virtual void SetUp() {
        tree = new AbducibleTree<ATTUtils_x101>();
    }

    virtual void TearDown() {
        delete tree;
    }
};

class SubsumerCoverer_102a : public ::testing::Test {
protected:

    AbducibleTree<ATTUtils_x102> *tree;

    virtual void SetUp() {
        tree = new AbducibleTree<ATTUtils_x102>();
    }

    virtual void TearDown() {
        delete tree;
    }
};

TEST_F(SubsumerBasic_101c, Init) { }

TEST_F(SubsumerBasic_101c, BasicInsertion) {
    tree->insert(ATAutoIntListWr({1}));
    tree->insert(ATAutoIntListWr({2, 3}));
    tree->insert(ATAutoIntListWr({4, 5, 6}));
    tree->insert(ATAutoIntListWr({1, 2, 3}));
    tree->insert(ATAutoIntListWr({4, 5, 9}));
}

TEST_F(SubsumerBasic_101c, InsertionEnsuredByContainment) {
    tree->insert(ATAutoIntListWr({1}));
    tree->insert(ATAutoIntListWr({2, 3}));
    tree->insert(ATAutoIntListWr({4, 5, 6}));
    tree->insert(ATAutoIntListWr({1, 2, 3}));
    tree->insert(ATAutoIntListWr({4, 5, 9}));

    ASSERT_TRUE(tree->contains(ATAutoIntListWr({1})));
    ASSERT_TRUE(tree->contains(ATAutoIntListWr({2, 3})));
    ASSERT_TRUE(tree->contains(ATAutoIntListWr({4, 5, 6})));
    ASSERT_TRUE(tree->contains(ATAutoIntListWr({1, 2, 3})));
    ASSERT_TRUE(tree->contains(ATAutoIntListWr({4, 5, 9})));

    ASSERT_FALSE(tree->contains(ATAutoIntListWr({3})));
    ASSERT_FALSE(tree->contains(ATAutoIntListWr({2, 3, 4})));
    ASSERT_FALSE(tree->contains(ATAutoIntListWr({4, 5, 6, 7})));
    ASSERT_FALSE(tree->contains(ATAutoIntListWr({1, 3, 4})));
    ASSERT_FALSE(tree->contains(ATAutoIntListWr({4, 5, 10})));
}

TEST_F(SubsumerBasic_101c, AutoSubsumes) {
    tree->insert(ATAutoIntListWr({4, 5, 6}));
    ASSERT_TRUE(tree->subsumes(ATAutoIntListWr({4, 5, 6})));
}

TEST_F(SubsumerBasic_101c, Subsets) {
    tree->insert(ATAutoIntListWr({4, 5, 6}));
    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({4, 5})));
    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({4, 6})));
    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({5, 6})));
    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({4})));
    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({5})));
    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({6})));
}

TEST_F(SubsumerBasic_101c, Supersets) {
    tree->insert(ATAutoIntListWr({4, 5}));
    ASSERT_TRUE(tree->subsumes(ATAutoIntListWr({4, 5, 6})));
    ASSERT_TRUE(tree->subsumes(ATAutoIntListWr({4, 5, 7})));
    ASSERT_TRUE(tree->subsumes(ATAutoIntListWr({1, 4, 5})));
    ASSERT_TRUE(tree->subsumes(ATAutoIntListWr({4, 2, 5})));
    ASSERT_TRUE(tree->subsumes(ATAutoIntListWr({5, 4, 3})));

    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({4, 6, 7})));
    ASSERT_FALSE(tree->subsumes(ATAutoIntListWr({1, 5, 9})));
}

TEST_F(SubsumerCoverer_102a, CleanerBasic) {
    tree->insert(ATAutoIntListWr({1, 2, 3}));
    ASSERT_TRUE(tree->contains(ATAutoIntListWr({1, 2, 3})));
    tree->insert(ATAutoIntListWr({4, 5, 6}));
    tree->cleanSubsumed(ATAutoIntListWr({1, 2}));

    ASSERT_TRUE(tree->contains(ATAutoIntListWr({4, 5, 6})));
    ASSERT_FALSE(tree->contains(ATAutoIntListWr({1, 2, 3})));
    // ASSERT_FALSE(tree->contains(ATAutoIntListWr({1, 2})));
}
*/
