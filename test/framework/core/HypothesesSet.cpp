#include <gtest/gtest.h>
#include <gpid/gpid.hpp>

#define HYPOTHESES_SET_TEST

#define HSET_SIZE 16

using namespace gpid;

class HypothesesSetTest : public ::testing::Test {
protected:
    HypothesesSetTest() { srand(time(NULL)); }

    HypothesesSet<int> set = HypothesesSet<int>(HSET_SIZE);

    virtual void SetUp() {
    }

    virtual void TearDown() {
    }
};

TEST_F(HypothesesSetTest, Example) {

}
