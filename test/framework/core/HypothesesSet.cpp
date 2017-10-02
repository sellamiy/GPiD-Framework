#include <gtest/gtest.h>
#include <gpid/gpid.hpp>

#define HYPOTHESES_SET_TEST

#define HSET_SIZE 16

using namespace gpid;

class HypothesesSetTest : public ::testing::Test {
protected:
    HypothesesSetTest() { srand(time(NULL)); }

    HypothesesSet<int> *set;

    virtual void SetUp() {
        set = new HypothesesSet<int>(HSET_SIZE);
    }

    virtual void TearDown() {
        delete set;
    }
};

TEST_F(HypothesesSetTest, InitStatus) {
    ASSERT_FALSE(set->isEmpty(0));
}
