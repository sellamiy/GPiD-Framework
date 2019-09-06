/**
 * \file minpart/generic-partitions.hpp
 * \brief Generic partition generator
 * \author Yanis Sellami
 * \date 2019
 */
#include <snlog/snlog.hpp>
#include <minpart/partitions.hpp>
#include <minpart/generalization-sets.hpp>

#ifndef LIB_MINPART_GENERIC_PARTITION__HEADER
#define LIB_MINPART_GENERIC_PARTITION__HEADER

namespace minpart {

    class GenericPartitionGenerator {
        /** \brief Last generated block-hypotheses. */
        gpartition blocks;
        /** \brief Last generated partition */
        gpartition partition;
        /** \brief Last number of block-hypotheses generated */
        size_t bsize = 0;
        /** \brief Last generated partition size */
        size_t psize = 0;

        size_t current_block = 0;
        size_t current_partition = 0;

        bool use_offset = false;
        size_t block_offset = 0;

        const PartitionGeneratorOptions opts;

        template<class Context> void
        compute_blocks(gsetid set, gsetid support, GSetEngine<Context>& engine);
        template<class Context> void
        compute_partition(gsetid set, gsetid support, GSetEngine<Context>& engine);

        void reinitialize();
        void offset_blocks();

        template<class Context> bool
        consistent_partition(gsetid setid, GSetEngine<Context>& engine);

        template<class Context> void
        create_block(gsetid setid, GSetEngine<Context>& engine);
        template<class Context> void
        create_partition_block(gsetid setid, GSetEngine<Context>& engine);

        inline void select_next_block();
        inline void select_next_partition();

        template<class Context>
        void generalize_block_location(size_t pos, const GSetEngine<Context>& engine);
        template<class Context>
        void generalize_partition_location(size_t pos, const GSetEngine<Context>& engine);

    public:
        GenericPartitionGenerator(const PartitionGeneratorOptions& opts)
            : block_offset(opts.offset), opts(opts) {}

        inline void signal_bmodels(size_t index) { block_offset += index; }
        inline void signal_bnotmodels() { block_offset = 0; }

        template<class Context> gpartition&
        generate_blocks(gsetid set, gsetid support, GSetEngine<Context>& engine);
        template<class Context> gpartition&
        generate_partition(gsetid set, gsetid support, GSetEngine<Context>& engine);

        template<class Context> inline bool
        blocks_covered_all(gsetid set, gsetid, const GSetEngine<Context>& engine) const {
            return opts.c_depth == 1 && opts.c_blocksize == engine.length(set);
        }
    };

    template<class Context> bool GenericPartitionGenerator::consistent_partition
    (gsetid setid, GSetEngine<Context>& engine) {
        gsetid recid = engine.merge(partition);
        return engine.equal(setid, recid);
    }

    template<class Context> void GenericPartitionGenerator::
    create_block(gsetid setid, GSetEngine<Context>& engine) {
        bsize++;
        blocks.push_back(engine.copy(setid));
    }

    template<class Context> void GenericPartitionGenerator::
    create_partition_block(gsetid setid, GSetEngine<Context>& engine) {
        psize++;
        partition.push_back(engine.copy(setid));
    }

    inline void GenericPartitionGenerator::select_next_block() {
        current_block++;
        if (current_block == bsize) current_block = 0;
    }

    inline void GenericPartitionGenerator::select_next_partition() {
        current_partition++;
        if (current_partition == psize) current_partition = 0;
    }

    template<class Context>
    void GenericPartitionGenerator::generalize_block_location
    (size_t pos, const GSetEngine<Context>& engine) {
        if (engine.is_generalizable_element(blocks[current_block], pos)) {
            engine.generalize_in_place(blocks.at(current_block), pos);
        }
    }

    template<class Context>
    void GenericPartitionGenerator::generalize_partition_location
    (size_t pos, const GSetEngine<Context>& engine) {
        if (engine.is_generalizable_element(partition[current_partition], pos)) {
            engine.generalize_in_place(partition[current_partition], pos);
        }
    }

    template<class Context>
    gpartition& GenericPartitionGenerator::generate_blocks
    (gsetid set, gsetid support, GSetEngine<Context>& engine) {
        reinitialize();
        compute_blocks(set, support, engine);

        if (use_offset) {
            offset_blocks();
        }

        return blocks;
    }

    template<class Context>
    gpartition& GenericPartitionGenerator::generate_partition
    (gsetid set, gsetid support, GSetEngine<Context>& engine) {
        compute_partition(set, support, engine);
        if (!consistent_partition(set, engine)) {
            snlog::l_warn() << "Engine generated an inconsistent partition!" << snlog::l_end;
        }
        return partition;
    }

#define MIN(a,b) ((a) < (b) ? (a) : (b))

    template<class Context>
    void GenericPartitionGenerator::compute_blocks
    (gsetid set, gsetid, GSetEngine<Context>& engine) {
        for (size_t i = 0; i < MIN(opts.c_blocksize, engine.length(set)); ++i) {
            create_block(set, engine);
        }
        for (size_t i = 0; i < engine.get_max_size(); ++i) {
            if (engine.is_generalizable_element(set, i)) {
                select_next_block();
                for (size_t j = 0; j < opts.c_depth; ++j) {
                    generalize_block_location(i, engine);
                }
            }
        }
    }

    template<class Context>
    void GenericPartitionGenerator::compute_partition
    (gsetid set, gsetid, GSetEngine<Context>& engine) {
        for (size_t i = 0; i < MIN(opts.p_blocksize, engine.length(set)); ++i) {
            create_partition_block(set, engine);
        }
        for (size_t i = 0; i < engine.get_max_size(); ++i) {
            if (engine.is_generalizable_element(set, i)) {
                select_next_partition();
                for (size_t j = 0; j < opts.p_depth; ++j) {
                    generalize_partition_location(i, engine);
                }
            }
        }
    }

#undef MIN

}

#endif
