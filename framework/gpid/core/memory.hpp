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

    /** Class for mapping indices to objects. */
    template<typename O>
    struct ObjectMapper {
        /** Object reference type */
        using index_t = uint32_t;

        /** Map a given reference to a given object in memory. */
        inline void map(index_t idx, O* l);
        /** Access an object in memory from its refence. */
        inline O& get(index_t idx);

        /** \return The number of mapped objects. */
        inline constexpr uint32_t size() const;

        /** Default constructor */
        ObjectMapper();
        /** Copy constructor */
        ObjectMapper(ObjectMapper<O>& o);
    private:
        std::map<index_t, O*> _mapping;
    };

    /**
     * \brief Allocate a named contiguous memory block for storage.
     *
     * This only allocates the memory range. If the memory block ends up
     * containing objects, those should be constructed using the
     * memoryObjectAllocation function.
     */
    template<typename O>
    inline void memoryRangeAllocation(const std::string id, size_t s) {
        starray::GAB_Status res;
        res = starray::requestContinuousArray(id, s, sizeof(O));
        if (res != starray::GAB_Status::SUCCESS) throw MemoryError("request for abducibles failed");
    }

    /**
     * \brief Allocate an object inside a named memory block.
     *
     * Used to construct object in a named memory block previously allocated
     * with the memoryRangeAllocation function.
     */
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

    template<typename O> ObjectMapper<O>::ObjectMapper() {}
    template<typename O> ObjectMapper<O>::ObjectMapper(ObjectMapper<O>& o)
        : _mapping(o._mapping) {}

    template<typename O>
    inline void ObjectMapper<O>::map(index_t idx, O* l) {
        _mapping[idx] = l;
    }

    template<typename O>
    inline O& ObjectMapper<O>::get(index_t idx) {
        return *_mapping[idx];
    }

    template<typename O>
    inline constexpr uint32_t ObjectMapper<O>::size() const {
        return _mapping.size();
    }

}

#endif
