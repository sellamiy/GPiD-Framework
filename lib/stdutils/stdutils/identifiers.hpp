/**
 * \file stdutils/identifiers.hpp
 * \brief Structure for generating identifiers
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_STANDARD_UTILS__IDENTIFIERS_HPP
#define LIB_STANDARD_UTILS__IDENTIFIERS_HPP

namespace stdutils {

    template <typename V>
    class id_box {
        V curr;
    public:
        id_box(const V& init) : curr(init) {}
        const V next() { return curr++; }
    };

}

#endif
