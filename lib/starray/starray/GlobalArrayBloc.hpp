/**
 * \file starray/GlobalArrayBloc.hpp
 * \brief Static memory ressources allocation.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef LIB_STARRAY__GLOBAL_ARRAY_BLOC_HPP
#define LIB_STARRAY__GLOBAL_ARRAY_BLOC_HPP

#include <cinttypes>
#include <string>

namespace starray {

    /** \brief Memory operation possible results. */
    enum GlobalArrayBlocStatus {
        /** The operation was successful */
        SUCCESS,
        /** Accessing memory for an unknown location */
        TAG_UNKNOWN,
        /** Operation conflicted as location already exists */
        TAG_DUPLICATION,
        /** Operation conflicted as location does not exist */
        TAG_UNALLOCATED,
        /** Out of bounds memory access */
        OOB_ACCESS,
        /** Access to an unconfigured memory location */
        UNCONFED_ACCESS,
        /** System allocation failure */
        ALLOCATION_FAILURE,
        /** Failed to configure as the memory location does not exist */
        UNALLOCATED_CONF_STORAGE
    };
    typedef GlobalArrayBlocStatus GAB_Status;

    /**
     * \brief Allocate a continuous memory location.
     * \param tag Unique tag representing the memory location.
     * \param elm_count Maximal number of elements in the collection.
     * \param elm_size Size of an element.
     *
     * Allocate a continuous memory location for storing an object collection.
     * The heap block allocated is of size at least elm_count * elm_size.
     * Elements reserved location starts at byte 0 of the block
     * and follows the block in a continous manner.
     *
     * \return SUCCESS if the block has been successfully allocated.
     * \return Any error code otherwise.
     */
    extern GAB_Status requestContinuousArray(std::string tag, uint32_t elm_count, size_t elm_size);

    /**
     * \brief Access a previously allocated memory region.
     * \param tag Unique tag referencing the memory region to access.
     * \param elm_pos Position of the element to access in the collection.
     * \param ptr Pointer reference for the accessed element.
     *
     * Access the memory region referenced by tag and previously allocated
     * and search for the element at position elm_pos in the collection.
     * Sets a pointer to this element in ptr.
     *
     * \return SUCCESS if the pointer to the element has been set.
     * \return Any error code otherwise.
     */
    extern GAB_Status accessContinuousPointer(std::string tag, uint32_t elm_pos, void** ptr);

};

#endif
