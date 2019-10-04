#include <iostream>
#include <stdutils/random.hpp>
#include <minpart/generic-partitions.hpp>

#define LIB_MINPART_GENERIC_PARTITIONS_SRC

using namespace minpart;

void GenericPartitionGenerator::reinitialize(size_t max_size) {
    bsize = 0;
    psize = 0;
    current_block = 0;
    current_partition = 0;
    blocks.clear();
    partition.clear();

    if (opts.random) {
        if (switchtable.empty()) {
            for (size_t i = 0; i < max_size; ++i) {
                switchtable.push_back(i);
            }
        }
        stdutils::shuffle(switchtable);
    }
}

void GenericPartitionGenerator::offset_blocks() {
    if (block_offset != 0) {
        for (size_t i = block_offset; i < bsize; ++i) {
            blocks[i-block_offset] = blocks[i];
        }
    }
    bsize -= block_offset;
}
