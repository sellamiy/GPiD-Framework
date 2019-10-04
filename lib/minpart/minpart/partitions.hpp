/**
 * \file minpart/partitions.hpp
 * \brief Partition utilities
 * \author Yanis Sellami
 * \date 2019
 */
#include <cstdlib>

#ifndef LIB_MINPART_PARTITION_UTILS__HEADER
#define LIB_MINPART_PARTITION_UTILS__HEADER

namespace minpart {

    struct PartitionGeneratorOptions {
        const size_t c_blocksize;
        const size_t c_depth;
        const size_t p_blocksize;
        const size_t p_depth;
        const bool offset;
        const bool random;
        PartitionGeneratorOptions
        (size_t c_blocksize, size_t c_depth, size_t p_blocksize, size_t p_depth, bool offset=true, bool random=false)
            : c_blocksize(c_blocksize), c_depth(c_depth),
              p_blocksize(p_blocksize), p_depth(p_depth),
              offset(offset), random(random)
        {}
    };

}

#endif
