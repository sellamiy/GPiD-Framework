/**
 * \file stdutils/random.hpp
 * \brief Misc. utils for randomizing stuff
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_STANDARD_UTILS__RANDOM_HPP
#define LIB_STANDARD_UTILS__RANDOM_HPP

#include <random>
#include <chrono>
#include <vector>
#include <algorithm>

namespace stdutils {

    static inline unsigned random_seed() {
        return std::chrono::system_clock::now().time_since_epoch().count();
    }

    template<class T> static void shuffle(std::vector<T>& v) {
        unsigned seed = random_seed();
        std::shuffle(v.begin(), v.end(), std::default_random_engine(seed));
    }

}

#endif
