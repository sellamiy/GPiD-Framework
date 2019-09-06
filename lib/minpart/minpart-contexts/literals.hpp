/**
 * \file minpart-contexts/literals.hpp
 * \brief Minimal partitioner literal example context
 * \author Yanis Sellami
 * \date 2019
 */
#include <vector>
#include <minpart/partitions.hpp>

#ifndef LIB_MINPART_CONTEXT_LITERALS__HEADER
#define LIB_MINPART_CONTEXT_LITERALS__HEADER

namespace minpart {
namespace literals {

    struct LiteralProblemOptions {
        size_t c_blocksize = 2;
        size_t c_depth = 1;
        size_t p_blocksize = 2;
        size_t p_depth = 1;

        size_t max_depth = 10;
        size_t min_depth = 0;

        std::vector<uint32_t> problem;
    };

    class LiteralProblemContext {
    public:
        using Options = LiteralProblemOptions;
    private:
        const Options opts;
    public:
        LiteralProblemContext(const Options& opts)
            : opts(opts)
        {}

        const PartitionGeneratorOptions generate_partition_options() const;

        inline size_t get_hypotheses_size() const { return opts.problem.size(); }

        inline uint32_t removal_level(uint32_t, size_t) const { return opts.max_depth + 1; }

        inline bool is_empty_element(uint32_t element, size_t) const {
            return element > opts.max_depth;
        }

        inline bool is_generalizable_element(uint32_t element, size_t) const {
            return element < opts.max_depth;
        }

        bool is_valid_hypothesis(const std::vector<uint32_t>& hyp) const;
        bool is_coherent_hypothesis(const std::vector<uint32_t>& hyp) const;

        void print(uint32_t element, size_t loc) const;

    };

}    
}

#endif
