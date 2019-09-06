#include <iostream>
#include <minpart/generic-partitions.hpp>

#define LIB_MINPART_GENERIC_PARTITIONS_SRC

using namespace minpart;

void GenericPartitionGenerator::reinitialize() {
    bsize = 0;
    psize = 0;
    current_block = 0;
    current_partition = 0;
    blocks.clear();
    partition.clear();
}

void GenericPartitionGenerator::offset_blocks() {
    if (block_offset != 0) {
        for (size_t i = block_offset; i < bsize; ++i) {
            blocks[i-block_offset] = blocks[i];
        }
    }
    bsize -= block_offset;
}
