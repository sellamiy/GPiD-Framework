/**
 * \file gpid/core/wrappers.hpp
 * \brief GPiD-Framework Core wrappers.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__WRAPPERS_HPP
#define GPID_FRAMEWORK__CORE__WRAPPERS_HPP

#include <map>

namespace gpid {

    /** \brief Class for mapping indices to literals. */
    template<class LiteralT>
    struct LiteralMapper {
        typedef uint32_t index_t;
        inline void map(index_t idx, LiteralT* l) { _mapping[idx] = l; }
        inline LiteralT& get(index_t idx) { return *_mapping[idx]; }
    private:
        std::map<index_t, LiteralT*> _mapping;
    };

}

#endif
