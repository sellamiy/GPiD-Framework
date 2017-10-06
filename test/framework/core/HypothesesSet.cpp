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

static HSTest_S hmemory[HSET_SIZE];

/* These tests assumes the hypothesis mapping works as expected. */
/* This hypothesis mapping should be tested elsewhere */

class HypothesesSetTest : public ::testing::Test {
protected:
    HypothesesSetTest() {
        srand(time(NULL));
        for (int i = 0; i < HSET_SIZE; i++) new (&(hmemory[i])) HSTest_S(i);
    }

    HypothesesSet<HSTest_S, HSTest_MW> *set;

    virtual void SetUp() {
        set = new HypothesesSet<HSTest_S, HSTest_MW>(HSET_SIZE);
        for (int i = 0; i < HSET_SIZE; i++) set->mapHypothesis(i, &(hmemory[i]));
    }

    virtual void TearDown() {
        delete set;
    }
};

TEST_F(HypothesesSetTest, InitNonEmpty) {
    ASSERT_FALSE(set->isEmpty(0));
}

TEST_F(HypothesesSetTest, InitSize) {
    ASSERT_EQ(set->getSourceSize(), (uint32_t)HSET_SIZE);
    ASSERT_EQ(set->getSize(), (uint32_t)HSET_SIZE);
}

TEST_F(HypothesesSetTest, RecoverFirstHypothesis) {
    uint32_t ssz = HSET_SIZE;
    HSTest_S& dat = set->nextHypothesis(0);
    /* Set status */
    ASSERT_EQ(set->getSourceSize(), ssz);
    ASSERT_EQ(set->getSize() + 1, ssz);
    ASSERT_FALSE(set->isEmpty(0));
    /* Content status */
    ASSERT_EQ(dat.data + 1, HSET_SIZE);
}

TEST_F(HypothesesSetTest, RecoverAllHypotheses) {
    uint32_t ssz = HSET_SIZE;
    int64_t inds = HSET_SIZE * (HSET_SIZE - 1) / 2;
    for (int i = HSET_SIZE; i > 0; i--) {
        ASSERT_FALSE(set->isEmpty(0)) << " @loop:" << i;
        HSTest_S& dat = set->nextHypothesis(0);
        /* Set status */
        ASSERT_EQ(set->getSourceSize(), ssz) << " @loop:" << i;
        ASSERT_EQ(set->getSize() + 1, (unsigned int)i) << " @loop:" << i;
        /* Content status */
        ASSERT_EQ(dat.data + 1, i);
        inds -= dat.data;
    }
    ASSERT_TRUE(set->isEmpty(0));
    ASSERT_EQ(inds, 0);
}
