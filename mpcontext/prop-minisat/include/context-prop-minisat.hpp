/**
 * \brief Minimal partitioner minisat propositional context
 * \author Yanis Sellami
 * \date 2019
 */
#include <vector>
#include <minisat/simp/SimpSolver.h>
#include <minpart/partitions.hpp>

#ifndef MINPART_CONTEXT_PROP_MINISAT__HEADER
#define MINPART_CONTEXT_PROP_MINISAT__HEADER

namespace minpart {
namespace prop {

    struct PropProblemOptions {
        size_t c_blocksize = 2;
        size_t c_depth = 1;
        size_t p_blocksize = 2;
        size_t p_depth = 1;

        bool random = false;

        std::string input_file;
    };

    struct PropExecOpts {
        PropProblemOptions local;
        bool deterministic = false;
    };

    class PropProblemContext {
    public:
        using Options = PropProblemOptions;
    private:
        const Options opts;

        Minisat::SimpSolver solver;
        Minisat::vec<Minisat::lbool> model;

        Minisat::vec<Minisat::lbool> checker;

        void assert_hypothesis(const std::vector<uint32_t>& hyp);
        bool check_modelling(bool expected=true);
        bool cmz_satisfied(const Minisat::Clause& c) const;
    public:
        PropProblemContext(const Options& opts);

        const PartitionGeneratorOptions generate_partition_options() const;

        inline size_t get_hypotheses_size() const { return solver.nVars(); }

        uint32_t removal_level(uint32_t, size_t) const { return 1; }

        bool is_empty_element(uint32_t element, size_t) const { return element > 0; }

        bool is_generalizable_element(uint32_t element, size_t) const { return element == 0; }

        bool is_valid_hypothesis(const std::vector<uint32_t>& hyp);
        bool is_coherent_hypothesis(const std::vector<uint32_t>& hyp);

        void print_problem() const;
        void print(uint32_t element, size_t loc) const;
    };

}    
}

#endif
