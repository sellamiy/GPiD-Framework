#include <gtest/gtest.h>
#include <atable/activable_tab.hpp>

#define STATIC_ATABLE_TEST

#define ARRAY_SIZE 16

using namespace atable;

class StaticActivableArrayTest : public ::testing::Test {
protected:
    StaticActivableArrayTest() { srand(time(NULL)); }

    StaticActivableArray *a;

    virtual void SetUp() {
        a = new StaticActivableArray(ARRAY_SIZE);;
    }

    virtual void TearDown() {
        delete a;
    }
};

TEST(StaticActivableArrayInitTest, Alloc) {
    StaticActivableArray *a;
    for (uint8_t i = 1; i < 255; i++) {
        a = new StaticActivableArray(i);
        delete a;
    }
}

TEST_F(StaticActivableArrayTest, ListCreation) {
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
        ASSERT_NE(a->has_next(), 0);
        ASSERT_EQ(a->get_next(), i);
    }
}

TEST_F(StaticActivableArrayTest, ActivatedSizeParameter) {
    for (uint8_t i = 0; i < 200; i++) {
        uint8_t doing = rand() % 2;
        uint8_t index = rand() % ARRAY_SIZE;
        // printf("index=%u\n", index);
        if (doing) {
            uint64_t tmp = a->get_activated_size();
            if (a->is_active(index)) {
                a->activate(index);
                // printf("1:%" PRIu64 ",%" PRIu64 "\n", tmp, a->get_activated_size());
                ASSERT_EQ(tmp, a->get_activated_size());
            } else {
                a->activate(index);
                // printf("2:%" PRIu64 ",%" PRIu64 "\n", tmp, a->get_activated_size());
                ASSERT_EQ(tmp, a->get_activated_size() - 1);
            }
        } else {
            uint64_t tmp = a->get_activated_size();
            if (a->is_active(index)) {
                a->deactivate(index);
                // printf("3:%" PRIu64 ",%" PRIu64 "\n", tmp, a->get_activated_size());
                ASSERT_EQ(tmp, a->get_activated_size() + 1);
            } else {
                a->deactivate(index);
                // printf("4:%" PRIu64 ",%" PRIu64 "\n", tmp, a->get_activated_size());
                ASSERT_EQ(tmp, a->get_activated_size());
            }
        }
    }
}

TEST_F(StaticActivableArrayTest, Activation) {
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
        ASSERT_NE(a->is_active(i), 0);
        a->deactivate(i);
        ASSERT_EQ(a->is_active(i), 0);
        a->activate(i);
        ASSERT_NE(a->is_active(i), 0);
    }
}

TEST_F(StaticActivableArrayTest, Deactivation) {
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
        ASSERT_NE(a->is_active(i), 0);
        a->deactivate(i);
        ASSERT_EQ(a->is_active(i), 0);
    }
}

TEST_F(StaticActivableArrayTest, ListCoherence1) {
    uint8_t seen[ARRAY_SIZE];
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) seen[i] = 0;
    a->deactivate(8);
    for (uint8_t i = 0; i < 15; i++) {
        ASSERT_NE(a->has_next(), 0);
        seen[a->get_next()] = 1;
    }
    ASSERT_EQ(a->has_next(), 0);
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
        if (i == 8) { ASSERT_EQ(seen[i], 0); }
        else { ASSERT_EQ(seen[i], 1); }
    }
}

TEST_F(StaticActivableArrayTest, ListCoherence21) {
    uint8_t seen[ARRAY_SIZE];
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) seen[i] = 0;
    a->deactivate(8);
    a->activate(8);
    a->deactivate(8);
    for (uint8_t i = 0; i < 15; i++) {
        ASSERT_NE(a->has_next(), 0);
        seen[a->get_next()] = 1;
    }
    ASSERT_EQ(a->has_next(), 0);
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
        if (i == 8) { ASSERT_EQ(seen[i], 0); }
        else { ASSERT_EQ(seen[i], 1); }
    }
}

TEST_F(StaticActivableArrayTest, ListCoherence25) {
    uint8_t seen[ARRAY_SIZE];
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) seen[i] = 0;
    a->deactivate(8);
    a->activate(8);
    a->deactivate(8);
    a->activate(8);
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
        ASSERT_NE(a->has_next(), 0);
        seen[a->get_next()] = 1;
    }
    ASSERT_EQ(a->has_next(), 0);
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) { ASSERT_EQ(seen[i], 1); }
}

TEST_F(StaticActivableArrayTest, ListCoherence2) {
    uint8_t seen[ARRAY_SIZE];
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) seen[i] = 0;
    a->deactivate(8);
    a->activate(8);
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
        ASSERT_NE(a->has_next(), 0);
        seen[a->get_next()] = 1;
    }
    ASSERT_EQ(a->has_next(), 0);
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) { ASSERT_EQ(seen[i], 1); }
}

TEST_F(StaticActivableArrayTest, ListCoherence3) {
    uint8_t seen[ARRAY_SIZE];
    uint8_t expected[ARRAY_SIZE];
    uint8_t expected_size = ARRAY_SIZE;
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) seen[i] = 0;
    for (uint8_t i = 0; i < ARRAY_SIZE; i++) expected[i] = 1;
    for (uint8_t k = 0; k < 200; k++) {
        uint8_t doing = rand() % 2;
        uint8_t index = rand() % ARRAY_SIZE;
        if (a->is_active(index)) {
            if (doing == 0) {
                expected[index] = 0;
                expected_size--;
            }
        } else {
            if (doing == 1) {
                expected[index] = 1;
                expected_size++;
            }
        }
        if (doing == 0) {
            a->deactivate(index);
        } else {
            a->activate(index);
        }
        for (uint8_t i = 0; i < expected_size; i++) {
            ASSERT_NE(a->has_next(), 0);
            seen[a->get_next()] = 1;
        }
        ASSERT_EQ(a->has_next(), 0);
        a->reset_iterator();
        for (uint8_t i = 0; i < ARRAY_SIZE; i++) {
            ASSERT_EQ(seen[i], expected[i]);
        }
        for (uint8_t i = 0; i < ARRAY_SIZE; i++) seen[i] = 0;
    }
}

TEST_F(StaticActivableArrayTest, ListResetIterator) {
    uint8_t cpt = 0;
    while (a->has_next()) {
        a->get_next();
        cpt++;
    }
    ASSERT_EQ(cpt, ARRAY_SIZE);
    cpt = 0;
    a->reset_iterator();
    while (a->has_next()) {
        a->get_next();
        cpt++;
    }
    ASSERT_EQ(cpt, ARRAY_SIZE);
}
