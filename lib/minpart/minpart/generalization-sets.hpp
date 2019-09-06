/**
 * \file minpart/generalization-sets.hpp
 * \brief Table wrappers for generazation sets
 * \author Yanis Sellami
 * \date 2019
 */
#include <map>
#include <ctime>
#include <vector>
#include <iostream>
#include <stdutils/identifiers.hpp>

#ifndef LIB_MINPART_GENERALIZATION_SETS__HEADER
#define LIB_MINPART_GENERALIZATION_SETS__HEADER

namespace minpart {

    inline const std::vector<uint32_t> random_vector(size_t size, size_t maxd, size_t mind) {
        std::vector<uint32_t> target(size);
        for (size_t i = 0; i < size; ++i) {
            target[i] = (rand() % (maxd - mind)) + mind;
        }
        return target;
    }

    using gsetcontent = uint32_t;
    using gset = std::vector<gsetcontent>;
    using gsetid = uint32_t;
    using gpartition = std::vector<gsetid>;

    template <class Context>
    class GSetEngine {
        Context& ctx;
        const size_t maxsize;
        stdutils::id_box<size_t> idbox;

        std::map<gsetid, std::shared_ptr<gset>> memory;

        uint64_t check_counter = 0;
    public:
        GSetEngine(Context& ctx)
            : ctx(ctx), maxsize(ctx.get_hypotheses_size())
        { }

        inline Context& get_context() const { return ctx; }

        inline size_t get_max_size() const { return maxsize; }
        inline uint64_t get_check_counter() const { return check_counter; }

        gsetid create();
        gsetid copy(gsetid src);

        inline bool equal(gsetid gs1, gsetid gs2) const {
            return *(memory.at(gs1)) == *(memory.at(gs2));
        }

        gsetid merge(gsetid gs1, gsetid gs2);
        gsetid merge(const gpartition& gpart, size_t except=-1);

        size_t length(gsetid gset) const;

        gsetid cleanup(gsetid hypid, gsetid supid);

        bool is_generalizable(gsetid hypid) const;
        inline bool is_generalizable_element(gsetid hypid, size_t elem) const {
            return ctx.is_generalizable_element((*memory.at(hypid))[elem], elem);
        }

        gsetid generalize_all(gsetid hypid);
        inline void generalize_in_place(gsetid hypid, size_t loc) const {
            (*memory.at(hypid)).at(loc)++;
        }

        bool is_satisfying(gsetid hypid);

        inline gsetid generate_full() { return create(); }
        gsetid generate_empty(Context& ctx);

        bool is_coherent(gsetid hypid) const;

        void print(gsetid hypid) const;
    };

    /* Context-dependent implementations */

    template <class Context>
    size_t GSetEngine<Context>::length(gsetid gset) const {
        size_t res = 0;
        for (size_t i = 0; i < maxsize; ++i) {
            if (!ctx.is_empty_element((*memory.at(gset))[i], i)) {
                ++res;
            }
        }
        return res;
    }

    template <class Context>
    gsetid GSetEngine<Context>::cleanup(gsetid hypid, gsetid supid) {
        gsetid resid = copy(hypid);
        gset& res = *memory.at(resid);
        gset& sup = *memory.at(supid);
        gset& hyp = *memory.at(hypid);
        for (size_t i = 0; i < maxsize; ++i) {
            if (res[i] >= sup[i]) {
                res[i] = ctx.removal_level(hyp[i], i);
            }
        }
        return resid;
    }

    template <class Context>
    bool GSetEngine<Context>::is_generalizable(gsetid hypid) const {
        for (size_t i = 0; i < maxsize; ++i) {
            if (ctx.is_generalizable_element((*memory.at(hypid))[i], i)) {
                return true;
            }
        }
        return false;
    }

    template <class Context>
    gsetid GSetEngine<Context>::generalize_all(gsetid hypid) {
        gsetid resid = copy(hypid);
        gset& res = *memory.at(resid);
        for (size_t i = 0; i < maxsize; ++i) {
            if (ctx.is_generalizable_element((*memory.at(hypid))[i], i)) {
                ++res[i];
            }
        }
        return resid;
    }

    template <class Context>
    bool GSetEngine<Context>::is_satisfying(gsetid hypid) {
        gset& hyp = *memory.at(hypid);
        check_counter += 1;
        bool res = ctx.is_valid_hypothesis(hyp);
        // old: instrumentation
        return res;
    }

    template <class Context>
    gsetid GSetEngine<Context>::generate_empty(Context& ctx) {
        gsetid resid = create();
        gset& res = *memory.at(resid);
        for (size_t i = 0; i < maxsize; ++i) {
            res[i] = ctx.removal_level(res[i], i);
        }
        return resid;
    }

    template <class Context>
    bool GSetEngine<Context>::is_coherent(gsetid hypid) const {
        gset& hyp = *memory.at(hypid);
        return ctx.is_coherent_hypothesis(hyp);
    }

    template <class Context>
    void GSetEngine<Context>::print(gsetid hypid) const {
        gset& hyp = *memory.at(hypid);
        for (size_t i = 0; i < maxsize; ++i) {
            // Warning: empty elements are ALSO printed!
            ctx.print(hyp[i], i);
        }
        std::cout << '\n' << std::endl;
    }

    template <class Context>
    gsetid GSetEngine<Context>::create() {
        std::shared_ptr<gset> ngset = std::shared_ptr<gset>(new gset(maxsize));
        gsetid id = idbox.next();
        memory[id] = ngset;
        return id;
    }

    template <class Context>
    gsetid GSetEngine<Context>::copy(gsetid src) {
        std::shared_ptr<gset> sgset = memory.at(src);
        std::shared_ptr<gset> ngset = std::shared_ptr<gset>(new gset(*sgset));
        gsetid id = idbox.next();
        memory[id] = ngset;
        return id;
    }

    template <class Context>
    gsetid GSetEngine<Context>::merge(gsetid gs1, gsetid gs2) {
        gsetid resid = copy(gs1);
        gset& res = *memory.at(resid);
        gset& sup = *memory.at(gs2);
        for (size_t i = 0; i < maxsize; ++i) {
            if (res[i] > sup[i]) {
                res[i] = sup[i];
            }
        }
        return resid;
    }

    template <class Context>
    gsetid GSetEngine<Context>::merge(const gpartition& gpart, size_t except) {
        // TODO: ensure that gpart has at least one element
        // TODO: except usage forces partitions to have less that MAX SIZE T - 1 elements
        gsetid resid = copy(gpart[except != 0 ? 0 : 1]);
        gset& res = *memory.at(resid);
        for (size_t i = 0; i < maxsize; ++i) {
            for (size_t j = 1; j < gpart.size(); ++j) {
                if (j != except) {
                    gset& sup = *memory.at(gpart[j]);
                    if (res[i] > sup[i]) {
                        res[i] = sup[i];
                    }
                }
            }
        }
        return resid;
    }

}

#endif
