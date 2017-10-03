#ifndef _GLOBAL_ARRAY_BLOC_HPP_
#define _GLOBAL_ARRAY_BLOC_HPP_

#include <inttypes.h>
#include <string>

namespace starray {

    enum GlobalArrayBlocStatus {
        SUCCESS,
        TAG_UNKNOWN,
        TAG_DUPLICATION,
        TAG_UNALLOCATED,
        OOB_ACCESS,
        UNCONFED_ACCESS,
        ALLOCATION_FAILURE,
        UNALLOCATED_CONF_STORAGE
    };
    typedef GlobalArrayBlocStatus GAB_Status;

    extern GAB_Status requestContinuousArray(std::string tag, uint32_t elm_count, size_t elm_size);
    extern GAB_Status accessContinuousPointer(std::string tag, uint32_t elm_pos, void** ptr);

};

#endif
