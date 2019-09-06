/**
 * \file minpart/minpart-algorithm.hpp
 * \brief Minimal partitioner algorithm
 * \author Yanis Sellami
 * \date 2019
 */
#include <stdutils/identifiers.hpp>
#include <minpart/generalization-sets.hpp>

#ifndef LIB_MINPART_ALG__HEADER
#define LIB_MINPART_ALG__HEADER

namespace minpart {

    template <class Context, class PartitionGenerator>
    gsetid compute_minimal_part
    (GSetEngine<Context>& engine, PartitionGenerator& generator,
     stdutils::id_box<size_t>& idbox, gsetid set, gsetid support, size_t node=0) {

        /* Update node identifer */
        size_t nextnode;
        if (node == 0) node = idbox.next();

        // old: print options

        /* Cleaning */
        size_t lb = engine.length(set);
        set = engine.cleanup(set, support);
        size_t lr = engine.length(set);

        if (lr != lb) {
            generator.signal_bnotmodels();
        }

        /* Base cases */
        if (!engine.is_generalizable(set)) {
            return set;
        }

        if (engine.length(set) == 1) {
            gsetid nset = engine.generalize_all(set);
            if (engine.is_satisfying(engine.merge(nset, support))) {
                nextnode = idbox.next();
                return compute_minimal_part
                    (engine, generator, idbox, nset, support, nextnode);
            } else {
                return set;
            }
        }

        /* Bloc generalization */
        const gpartition blocks = generator.generate_blocks(set, support, engine);
        for (size_t i = 0; i < blocks.size(); ++i) {
            if (engine.is_satisfying(engine.merge(blocks[i], support))) {
                generator.signal_bmodels(i);
                nextnode = idbox.next();
                return compute_minimal_part
                    (engine, generator, idbox, blocks[i], support, nextnode);
            }
        }

        /* Hack stopping if all possibilities have already been tested */
        if (generator.blocks_covered_all(set, support, engine)) {
            return set;
        }

        /* Partitioning */
        gpartition partition = generator.generate_partition(set, support, engine);
        for (size_t i = 0; i < partition.size(); ++i) {
            generator.signal_bnotmodels();
            nextnode = idbox.next();
            partition[i] = compute_minimal_part
                (engine, generator, idbox,
                 partition[i], engine.merge(engine.merge(partition, i), support),
                 nextnode);
        }

        return engine.merge(partition);
    }
    
}

#endif
