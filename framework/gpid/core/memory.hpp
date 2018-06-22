/**
 * \file gpid/core/memory.hpp
 * \brief GPiD-Framework Memory Handlers.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__MEMORY_HPP
#define GPID_FRAMEWORK__CORE__MEMORY_HPP

#include <map>
#include <gpid/core/errors.hpp>
#include <starray/starray.hpp>

namespace gpid {

    /** \brief Class for mapping indices to objects. */
    template<typename O>
    struct ObjectMapper {
        using index_t = uint32_t;
        
        inline void map(index_t idx, O* l);
        inline O& get(index_t idx);
        
        inline uint32_t size();
    private:
        std::map<index_t, O*> _mapping;
    };

    template<typename O>
    inline void memoryRangeAllocation(const std::string id, size_t s) {
        starray::GAB_Status res;
        res = starray::requestContinuousArray(id, s, sizeof(O));
        if (res != starray::GAB_Status::SUCCESS) throw MemoryError("request for abducibles failed");
    }

    template<typename O, typename ... ObjectParameters>
    inline void memoryObjectAllocation
    (const std::string id, uint32_t pos, ObjectMapper<O>& mapper, ObjectParameters... opars) {
        O *mloc;
        starray::GAB_Status res;
        res = starray::accessContinuousPointer(id, pos, (void**)&mloc);
        if (res != starray::GAB_Status::SUCCESS) throw MemoryError("access for abducibles failed");
        new (mloc) O(opars...);
        mapper.map(pos, mloc);
    }

    /* *** Implementations *** */

    template<typename O>
    inline void ObjectMapper<O>::map(index_t idx, O* l) {
        _mapping[idx] = l;
    }

    template<typename O>
    inline O& ObjectMapper<O>::get(index_t idx) {
        return *_mapping[idx];
    }

    template<typename O>
    inline uint32_t ObjectMapper<O>::size() {
        return _mapping.size();
    }

}

#endif
