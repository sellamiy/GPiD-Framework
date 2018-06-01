#include <vector>
#include <gtest/gtest.h>
#include <gpid/gpid.hpp>

#define ABDUCIBLE_TREE_TEST

using namespace gpid;

struct ATAutoIntWr {
    uint32_t v;
    ATAutoIntWr() : v(0) {}
    ATAutoIntWr(const ATAutoIntWr& o) : v(o.v) {}
    ATAutoIntWr(const uint32_t u) : v(u) {}
    bool operator < (const ATAutoIntWr& o) const { return v < o.v; }
};

typedef ObjectMapper<ATAutoIntWr> LiteralMapperT;
typedef LiteralHypothesis LiteralHypothesisT;

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

    typedef ATAutoIntWr LiteralT;

    unsigned int _lvl = 0;
    std::vector<unsigned int> _lvs;
    std::vector<LiteralT> _data;

    void addLiteral(LiteralT f, bool) { _data.push_back(f); }

    void push() { _lvs.push_back(_data.size()); }

    void pop() { _lvl = _lvs.back(); _lvs.pop_back(); while(_data.size() > _lvl) _data.pop_back(); }

};

#warning Incomplete update here!

/*
struct ATAutoSolver : public ATSolverZero {

    SolverTestStatus check() {
        for (unsigned int i=0; i < _lvs.back(); ++i) {
            if (subsets(_data[i], _data.back())) return SolverTestStatus::UNSAT;
        }
        return SolverTestStatus::SAT;
    }

};

struct ATRevoSolver : public ATSolverZero {

    SolverTestStatus check() {
        std::vector<unsigned int> _ndata;
        for (unsigned int i=1; i < _data.size(); ++i) _ndata.push_back(_data[i][0].v);
        if (subsets(_data[0], ATAutoIntListWr(_ndata))) return SolverTestStatus::UNSAT;
        return SolverTestStatus::SAT;
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

struct ATTUtils_x101 : public ATAutoSolver {
    typedef ATAutoSolver InterfaceT;
};

struct ATTUtils_x102 : public ATRevoSolver {
    typedef ATRevoSolver InterfaceT;
};

template <class CInterfaceT>
struct SolverEngineT {
    typedef CInterfaceT InterfaceT;
    typedef typename CInterfaceT::LiteralT LiteralT;
};

#define MAPPING_MAX_SIZE 256

template <class CSolverEngineT>
class Subsumer : public::testing::Test {
protected:

    CSolverEngineT se;
    LiteralMapperT mapper;
    LiteralHypothesisT chyp = LiteralHypothesisT(MAPPING_MAX_SIZE);
    AbducibleTree<CSolverEngineT> *tree;

    virtual void SetUp() {
        tree = new AbducibleTree<CSolverEngineT>(se, mapper);
        for (int i = 0; i < MAPPING_MAX_SIZE; i++) {
            mapper.map(i, ATAutoIntWr(i));
        }
    }

    virtual void TearDown() {
        delete tree;
    }

    inline void addLit(int l) { chyp.addLiteral(l, 1); }
    inline void clearLits() { chyp.removeLiterals(1); }

    inline void executeBasicInsertions() {
        addLit(1);
        tree->insert(chyp);
        clearLits();

        addLit(2);
        addLit(3);
        tree->insert(chyp);
        clearLits();

        addLit(4);
        addLit(5);
        addLit(6);
        tree->insert(chyp);
        clearLits();

        addLit(1);
        addLit(2);
        addLit(3);
        tree->insert(chyp);
        clearLits();

        addLit(4);
        addLit(5);
        addLit(9);
        tree->insert(chyp);
        clearLits();
    }
};

typedef Subsumer<SolverEngineT<ATTUtils_x101>> SubsumerBasic_101c;
typedef Subsumer<SolverEngineT<ATTUtils_x102>> SubsumerCoverer_102a;

TEST_F(SubsumerBasic_101c, Init) { }

TEST_F(SubsumerBasic_101c, BasicInsertion) {
    executeBasicInsertions();
}

TEST_F(SubsumerBasic_101c, InsertionEnsuredByContainment) {
    executeBasicInsertions();

    addLit(1);
    ASSERT_TRUE(tree->contains(chyp));
    clearLits();

    addLit(2);
    addLit(3);
    ASSERT_TRUE(tree->contains(chyp));
    clearLits();

    addLit(4);
    addLit(5);
    addLit(6);
    ASSERT_TRUE(tree->contains(chyp));
    clearLits();

    addLit(1);
    addLit(2);
    addLit(3);
    ASSERT_TRUE(tree->contains(chyp));
    clearLits();

    addLit(4);
    addLit(5);
    addLit(9);
    ASSERT_TRUE(tree->contains(chyp));
    clearLits();

    addLit(3);
    ASSERT_FALSE(tree->contains(chyp));
    clearLits();

    addLit(2);
    addLit(3);
    addLit(4);
    ASSERT_FALSE(tree->contains(chyp));
    clearLits();

    addLit(4);
    addLit(5);
    addLit(6);
    addLit(7);
    ASSERT_FALSE(tree->contains(chyp));
    clearLits();

    addLit(1);
    addLit(3);
    addLit(4);
    ASSERT_FALSE(tree->contains(chyp));
    clearLits();

    addLit(4);
    addLit(5);
    addLit(10);
    ASSERT_FALSE(tree->contains(chyp));
    clearLits();
}

TEST_F(SubsumerBasic_101c, AutoSubsumes) {
    addLit(4);
    addLit(5);
    addLit(6);
    tree->insert(chyp);
    ASSERT_TRUE(tree->fwdSubsumes(chyp));
    clearLits();
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
