#include <gtest/gtest.h>
#include <gpid/gpid.hpp>

#define HYPOTHESES_SET_TEST

#define HSET_SIZE 16

using namespace gpid;

struct HSTest_S {
    int data;
    HSTest_S()            : data(0)      {}
    HSTest_S(int d)       : data(d)      {}
    HSTest_S(HSTest_S& d) : data(d.data) {}
};

struct HSTest_MW {};

struct HSTest_SW {};

struct HSTest_SWrapper {
    typedef HSTest_S HypothesisT;
    typedef HSTest_MW ModelT;
    typedef HSTest_MW StorageT;
};

static HSTest_S hmemory[HSET_SIZE];

/* These tests assumes the hypothesis mapping works as expected. */
/* This hypothesis mapping should be tested elsewhere */

class HypothesesSetTest : public ::testing::Test {
protected:
    HypothesesSetTest() {
        srand(time(NULL));
        for (int i = 0; i < HSET_SIZE; i++) new (&(hmemory[i])) HSTest_S(i);
    }

    HSTest_SWrapper glob;
    HypothesesSet<HSTest_SWrapper> *set;

    virtual void SetUp() {
        set = new HypothesesSet<HSTest_SWrapper>(glob, HSET_SIZE);
        for (int i = 0; i < HSET_SIZE; i++) set->mapHypothesis(i, &(hmemory[i]));
    }

    virtual void TearDown() {
        delete set;
    }
};

TEST_F(HypothesesSetTest, InitNonEmpty) {
    ASSERT_TRUE(set->nextHypothesis(1));
}

TEST_F(HypothesesSetTest, InitSize) {
    ASSERT_EQ(set->getSourceSize(), (uint32_t)HSET_SIZE);
    // ASSERT_EQ(set->getSize(), (uint32_t)HSET_SIZE);
}

TEST_F(HypothesesSetTest, RecoverFirstHypothesis) {
    uint32_t ssz = HSET_SIZE;
    set->nextHypothesis(1);
    HSTest_S& dat = set->getHypothesis();
    /* Set status */
    ASSERT_EQ(set->getSourceSize(), ssz);
    // ASSERT_EQ(set->getSize() + 1, ssz);
    ASSERT_TRUE(set->nextHypothesis(1));
    /* Content status */
    ASSERT_EQ(dat.data + 1, HSET_SIZE);
}

TEST_F(HypothesesSetTest, RecoverAllHypotheses) {
    uint32_t ssz = HSET_SIZE;
    int64_t inds = HSET_SIZE * (HSET_SIZE - 1) / 2;
    for (int i = HSET_SIZE; i > 0; i--) {
        bool has_next = set->nextHypothesis(1);
        ASSERT_TRUE(has_next) << " @loop:" << i;
        HSTest_S& dat = set->getHypothesis();
        /* Set status */
        ASSERT_EQ(set->getSourceSize(), ssz) << " @loop:" << i;
        // ASSERT_EQ(set->getSize() + 1, (unsigned int)i) << " @loop:" << i;
        /* Content status */
        ASSERT_EQ(dat.data + 1, i);
        inds -= dat.data;
    }
    ASSERT_FALSE(set->nextHypothesis(1));
    ASSERT_EQ(inds, 0);
}

TEST_F(HypothesesSetTest, FirstAndSecondSublevel) {
    bool has_next;
    // First Hyp
    has_next = set->nextHypothesis(1);
    ASSERT_TRUE(has_next);
    ASSERT_EQ(set->getHypothesis().data + 1, HSET_SIZE);
    // No Hyp
    has_next = set->nextHypothesis(2);
    ASSERT_FALSE(has_next);
    // Second Hyp
    has_next = set->nextHypothesis(1);
    ASSERT_TRUE(has_next);
    ASSERT_EQ(set->getHypothesis().data + 2, HSET_SIZE);
    // Has 1 Hyp
    has_next = set->nextHypothesis(2);
    ASSERT_TRUE(has_next);
    ASSERT_EQ(set->getHypothesis().data + 1, HSET_SIZE);
    has_next = set->nextHypothesis(2);
    ASSERT_FALSE(has_next);
    // Pursue
    has_next = set->nextHypothesis(1);
    ASSERT_TRUE(has_next);
    ASSERT_EQ(set->getHypothesis().data + 3, HSET_SIZE);
}
