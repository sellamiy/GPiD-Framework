/**
 * \brief Minimal partitioner cvc4 sl context
 * \author Yanis Sellami
 * \date 2019
 */
#include <vector>
#include <cvc4/cvc4.h>
#include <minpart/partitions.hpp>

#ifndef MINPART_CONTEXT_SL_CVC4__HEADER
#define MINPART_CONTEXT_SL_CVC4__HEADER

namespace minpart {
namespace slcvc {

    /**
     * \brief Sign of a separation subformula.
     */
    enum class CVC4_ExprDualSign {
        CVC4_DS_EQ,
        CVC4_DS_NEQ,
        CVC4_DS_UNDEF
    };

    /**
     * \brief Structure for storing subformula parameters information.
     *
     * This structure is a contraction of the subelement formula meant
     * as a storage medium. It allows for the construction of the
     * associated subformula.
     */
    struct CVC4_ExprDual {
        /** \brief Source subelement expressions. */
        CVC4::Expr df;
        /** \brief Target subelement expressions. */
        CVC4::Expr dt;
        /** \brief Sign of the subelement formula. */
        CVC4_ExprDualSign sign;
        /**
         * \brief Basic constructor for subelement storage medium.
         * \param f - Source expression.
         * \param t - Target expression.
         * \param s - Sign of the subelement.
         */
        inline CVC4_ExprDual
        (const CVC4::Expr& f, const CVC4::Expr& t, const CVC4_ExprDualSign s)
            : df(f), dt(t), sign(s) {}
    };
    /** \brief Separation element storage structure. */
    using CVC4_ExprWrapper = std::vector<std::shared_ptr<CVC4_ExprDual>>;

    enum class SLInputMode { File, Local };

    struct SLProblemOptions {
        size_t c_blocksize = 2;
        size_t c_depth = 1;
        size_t p_blocksize = 2;
        size_t p_depth = 1;

        bool random = false;

        CVC4::ExprManager& em;

        SLInputMode mode;
        std::string input_file;

        std::shared_ptr<CVC4::Expr> fml;
        CVC4_ExprWrapper mmt;
        size_t sep0;
        size_t sep1;

        SLProblemOptions(CVC4::ExprManager& em)
            : em(em), mode(SLInputMode::File)
        { }
    };

    struct SLExecOpts {
        CVC4::ExprManager em;
        slcvc::SLProblemOptions local;
        bool deterministic;

        SLExecOpts() : local(em), deterministic(false) {}
    };

    class SLProblemContext {
    public:
        using Options = SLProblemOptions;
    private:
        const Options opts;

        size_t hyp_size;

        CVC4::ExprManager& em;
        CVC4::SmtEngine smt;

        CVC4::Expr& formula;
        CVC4::Expr lcl_formula;
        CVC4::Expr bld_formula;
        CVC4_ExprWrapper model_matchTable;

        // Models in HySets : [Separation Formulas] [Equalities, disequalities] [Eventual emp]
        size_t separator_0; // First index in model corresponding to equalities/disequalities
        size_t separator_1; // First index in model corresponding to emp

        void compute_expression(uint32_t element, size_t index);
        void compute_assertion(const std::vector<uint32_t>& hyp);

        void clear_engine();
        void assert_model_formula(bool positive=false);
        void assert_hypothesis(const std::vector<uint32_t>& hyp);
        bool engine_query(bool expected=false, bool notify_ukn=true);
    public:
        SLProblemContext(const Options& opts);

        const PartitionGeneratorOptions generate_partition_options() const;

        inline size_t get_hypotheses_size() const { return hyp_size; }

        uint32_t removal_level(uint32_t, size_t) const;

        bool is_empty_element(uint32_t element, size_t) const;

        bool is_generalizable_element(uint32_t element, size_t) const;

        bool is_valid_hypothesis(const std::vector<uint32_t>& hyp);
        bool is_coherent_hypothesis(const std::vector<uint32_t>& hyp);

        void print_problem() const;
        void print(uint32_t element, size_t loc);
    };


}    
}

#endif
