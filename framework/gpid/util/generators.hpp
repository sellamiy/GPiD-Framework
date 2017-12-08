/**
 * \file gpid/util/generators.hpp
 * \brief Wrappers for abducibles generation
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__UTIL__GENERATORS_HPP
#define GPID_FRAMEWORK__UTIL__GENERATORS_HPP

#include <gpid/core/hypotheses.hpp>

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
        if (res != starray::GAB_Status::SUCCESS) throw MemoryError("request for abducibles failed");
    }

    template <typename HypothesesSetT, typename HypothesisInternalT>
    static inline void store_gab_hyp
    (HypothesesSetT& set, uint32_t pos, HypothesisInternalT cstl) {
        typename HypothesesSetT::HypothesisT *mloc;
        starray::GAB_Status res;
        res = starray::accessContinuousPointer(last_gab_tab(), pos, (void**)&mloc);
        if (res != starray::GAB_Status::SUCCESS) throw MemoryError("access for abducibles failed");
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
            throw InternalError("unknown abducible input type: " + std::to_string(opts.input_type));
        }
    }

    template <typename ProblemT, typename HypothesesSetT, typename LoaderT>
    static inline void loadAbducibles
    (std::string filename, typename ProblemT::ContextManagerT& ctx,
     typename ProblemT::DeclarationsT& decls, HypothesesSetT& set) {
        alloc_gab<typename HypothesesSetT::HypothesisT>(set.getSourceSize());
        std::map<int, int> linker;
        AbducibleParser parser(filename);
        parser.init();
        for (uint32_t i = 0; i < set.getSourceSize(); i++) {
            if (!parser.isOk()) {
                throw ParseError("Error loading from @file:" + filename);
            }
            LoaderT()(i, parser.nextAbducible(), ctx, decls, set, linker);
        }
    }

    template <typename ProblemT, typename HypothesesSetT, typename GeneratorT, typename LoaderT>
    static inline void generateAbducibles
    (AbduciblesOptions& opts, typename ProblemT::ContextManagerT& ctx,
     typename ProblemT::DeclarationsT& decls, HypothesesSetT& set) {
        if (opts.input_type == AbdInputType::ABDIT_FILE) {
            loadAbducibles<ProblemT, HypothesesSetT, LoaderT>(opts.input_file, ctx, decls, set);
        } else if (opts.input_type == AbdInputType::ABDIT_GENERATOR) {
            GeneratorT()(opts.input_generator, ctx, decls, set);
        } else {
            throw InternalError("unknown abducible input type: " + std::to_string(opts.input_type));
        }
    }

};

#endif
