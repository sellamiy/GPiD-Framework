#include <gtest/gtest.h>
#include <ugly/ugly.hpp>

#define BEURK_TABLES_TEST

using namespace ugly;

struct BTTM2Refuser {
    inline bool operator()(uint32_t insert, uint32_t other) {
        return insert == 2*other;
    }
};

struct BTTM2Cleaner {
    inline bool operator()(uint32_t insert, uint32_t other) {
        return other == 2*insert;
    }
};

class BeurkTablesTest : public ::testing::Test {
protected:
    BeurkTablesTest() { srand(time(NULL)); }

    BeurkTable<uint32_t, BTTM2Refuser, BTTM2Cleaner> *t;

    virtual void SetUp() {
        t = new BeurkTable<uint32_t, BTTM2Refuser, BTTM2Cleaner>();
    }

    virtual void TearDown() {
        delete t;
    }
};

TEST_F(BeurkTablesTest, InitialState) {
    ASSERT_TRUE(t->free_location(0));
    ASSERT_FALSE(t->used_location(0));
    ASSERT_EQ(t->size(), 0);
}

TEST_F(BeurkTablesTest, InitialInsertions) {
    for (unsigned int i=0; i < 5; i++) t->insert(i);
    ASSERT_EQ(t->size(), 5);
}

TEST_F(BeurkTablesTest, Refuser) {
    t->insert(1);
    ASSERT_EQ(t->size(), 1);
    t->insert_refuse(2);
    ASSERT_EQ(t->size(), 1);
    t->insert_refuse(3);
    ASSERT_EQ(t->size(), 2);
    t->insert_refuse(6);
    ASSERT_EQ(t->size(), 2);
    t->insert_refuse(5);
    ASSERT_EQ(t->size(), 3);
    t->insert_refuse(2);
    t->insert_refuse(6);
    ASSERT_EQ(t->size(), 3);
}

TEST_F(BeurkTablesTest, Cleaner) {
    t->insert(1);
    t->insert(4);
    t->insert(6);
    t->insert(22);
    ASSERT_EQ(t->size(), 4);
    t->insert_clean(2);
    ASSERT_EQ(t->size(), 4);
    t->insert_clean(3);
    ASSERT_EQ(t->size(), 4);
    t->insert_clean(11);
    ASSERT_EQ(t->size(), 4);
    t->insert_clean(22);
    ASSERT_EQ(t->size(), 5);
}
