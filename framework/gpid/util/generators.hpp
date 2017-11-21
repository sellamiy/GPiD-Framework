#ifndef GPID_FRAMEWORK__UTIL__GENERATORS_HPP
#define GPID_FRAMEWORK__UTIL__GENERATORS_HPP

#include <snlog/snlog.hpp>
#include <starray/starray.hpp>
#include <gpid/core/hypotheses.hpp>
#include <gpid/options/options_abducibles.hpp>

namespace gpid {

    static std::string gpg_gab_tag = "Abducibles";
    static int gpg_gab_key = 0;
    static inline std::string next_gab_tab()
    { return gpg_gab_tag + std::to_string(++gpg_gab_key); }
    static inline std::string last_gab_tab()
    { return gpg_gab_tag + std::to_string(gpg_gab_key); }

    template <typename HypothesisT>
    static inline void alloc_gab(uint32_t size) {
        starray::GAB_Status res;
        res = starray::requestContinuousArray(next_gab_tab(), size, sizeof(HypothesisT));
        snlog::t_error(res != starray::GAB_Status::SUCCESS, "Memory request for abducibles failed!");
    }

    template <typename HypothesesSetT, typename HypothesisInternalT>
    static inline void store_gab_hyp
    (HypothesesSetT& set, uint32_t pos, HypothesisInternalT cstl) {
        typename HypothesesSetT::HypothesisT *mloc;
        starray::GAB_Status res;
        res = starray::accessContinuousPointer(last_gab_tab(), pos, (void**)&mloc);
        snlog::t_error(res != starray::GAB_Status::SUCCESS, "Memory access for abducibles failed!");
        new (mloc) typename HypothesesSetT::HypothesisT(cstl);
        set.mapHypothesis(pos, mloc);
    }

    template <typename ProblemT, typename GeneratorCounterT>
    static inline uint32_t countAbducibles(AbduciblesOptions& opts, ProblemT& pbl) {
        if (opts.input_type == AbdInputType::ABDIT_FILE) {
            return getAbducibleCount(opts.input_file);
        } else if (opts.input_type == AbdInputType::ABDIT_GENERATOR) {
            return GeneratorCounterT()(opts.input_generator, pbl);
        } else {
            snlog::l_internal("Unknown abducible input type: " + std::to_string(opts.input_type));
            return 0;
        }
    }

    template <typename HypothesesSetT, typename ContextT, typename DeclarationsT,
              typename LoaderT, typename GeneratorT>
    static inline void generateAbducibles
    (AbduciblesOptions& opts, ContextT& ctx, DeclarationsT& decls, HypothesesSetT& set) {
        if (opts.input_type == AbdInputType::ABDIT_FILE) {
            LoaderT()(opts.input_file, ctx, decls, set);
        } else if (opts.input_type == AbdInputType::ABDIT_GENERATOR) {
            GeneratorT()(opts.input_generator, ctx, decls, set);
        } else {
            snlog::l_internal("Unknown abducible input type: " + std::to_string(opts.input_type));
        }
    }

};

#endif
