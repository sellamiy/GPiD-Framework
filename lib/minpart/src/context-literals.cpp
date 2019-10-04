#include <iostream>
#include <minpart-contexts/literals.hpp>

#define LIB_CONTEXT_LITERALS_SRC

using namespace minpart;
using namespace minpart::literals;

const PartitionGeneratorOptions LiteralProblemContext::generate_partition_options() const {
        PartitionGeneratorOptions
            result(opts.c_blocksize, opts.c_depth, opts.p_blocksize, opts.p_depth,
                   true, opts.random);
        return result;
}

bool LiteralProblemContext::is_valid_hypothesis(const std::vector<uint32_t>& hyp) const {
    if (hyp.size() != opts.problem.size()) return false;
    for (size_t i = 0; i < opts.problem.size(); ++i) {
        if (hyp[i] > opts.problem[i]) {
            return false;
        }
    }
    return true;
}

bool LiteralProblemContext::is_coherent_hypothesis(const std::vector<uint32_t>& hyp) const {
    if (hyp.size() != opts.problem.size()) return false;
    for (size_t i = 0; i < opts.problem.size(); ++i) {
        if (hyp[i] != opts.problem[i]) {
            return false;
        }
    }
    return true;
}

void LiteralProblemContext::print(uint32_t element, size_t loc) const {
    std::cout << loc << "." << element << "  ";
}
