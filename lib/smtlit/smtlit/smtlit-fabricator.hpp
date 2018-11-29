#ifndef LIB_SMTLIB2_LITERAL_TOOLS__FABRICATOR__HEADER
#define LIB_SMTLIB2_LITERAL_TOOLS__FABRICATOR__HEADER

#include <smtlit/smtlit-config.hpp>

namespace smtlit {

    enum class FabricationPolicy {
        Apply_Simple, Apply_Symmetric
    };

    enum class FilterMode { Conjunctive, Disjunctive };

    enum class FilterPolicy {
        Type_Include,
        Type_Exclude,
        Annotation_Include,
        Annotation_Exclude,
        Content_Include,
        Content_Exclude
    };
    using FilterData = std::string;

    struct FabricationFilter {
        const FilterPolicy policy;
        const FilterData data;
        FabricationFilter(const FilterPolicy policy, const FilterData& data)
            : policy(policy), data(data) {}
        FabricationFilter(const FabricationFilter& o)
            : policy(o.policy), data(o.data) {}
        bool accept(const smtlit_t& l, const smtannotation_map& annots) const;
    };

    class WorkRule {
        FilterMode mode;
        std::vector<FabricationFilter> filters;
    public:
        WorkRule(FilterMode mode) : mode(mode) {}
        inline void add_filter(const FabricationFilter& f) { filters.push_back(f); }
        inline bool accept(const smtlit_t& l, const smtannotation_map& annots) const;
        inline bool accept_conj(const smtlit_t& l, const smtannotation_map& annots) const;
        inline bool accept_disj(const smtlit_t& l, const smtannotation_map& annots) const;
    };

    class FabricationRule : public WorkRule {
        const FabricationPolicy policy;
        const smtfun_t fun;
        const smtparam_binding_set default_binds;
        const smtannotation_t end_annotation;

        bool valid(param_iterator_set& pset, const smttype_map& src) const;
        void next(param_iterator_set& pset, const smttype_map& src) const;
        bool accept_bind(param_iterator_set& pset, const smtannotation_map& annots) const;
    public:
        FabricationRule(FilterMode mode, FabricationPolicy policy, const smtfun_t& fun,
                        const smtannotation_t annot="<?>")
            : WorkRule(mode), policy(policy), fun(fun), end_annotation(annot) {}
        FabricationRule(FilterMode mode, FabricationPolicy policy, const smtfun_t& fun,
                        const smtparam_binding_set& binds, const smtannotation_t annot="<?>")
            : WorkRule(mode), policy(policy), fun(fun),
              default_binds(binds), end_annotation(annot) {}

        inline const smtfun_t& get_fun() const { return fun; }
        inline const smtannotation_t& get_annotation() const { return end_annotation; }

        smtparam_binding_set select(param_iterator_set& pset, const smttype_map& src,
                                    const smtannotation_map& annots) const;
        inline void update(smtparam_binding_set& binds) const;
        inline smtlit_t generate(const smtparam_binding_set& binds) const;
        inline const std::set<smtparam_size_t> unbound() const;
    };

    using FiltrationRule = WorkRule;

    class SmtFunStorage {
        smtfun_set funs;
        smttype_map _types;
        smtannotation_map _annots;
    public:
        inline const smtfun_set& get_funs() const { return funs; }
        inline void annotate(const smtident_t& f, const smtannotation_t& a);
        inline void insert(const smtfun_t& f);
        inline void insert(const smtfun_t& f, const smtannotation_t& a);
    };

    class SmtLitFabricator {
        smtlit_set lits;
        smttype_map _types;
        smtannotation_map _annots;

        std::set<smtlit_t> filtered;
    public:
        inline const smtlit_set& get_lits() const { return lits; }
        inline const std::set<smtlit_t>& get_filtered() const { return filtered; }
        inline const std::set<smtident_t>& get_annotated(const smtannotation_t& annot) const
        { return _annots.at(annot); }

        inline void annotate(const smtident_t& l, const smtannotation_t& a);
        inline void insert(const smtlit_t& l);
        inline void insert(const smtlit_t& l, const smtannotation_t& a);

        inline const std::set<smtlit_t>& filter(const FiltrationRule& frule, bool reset=false);

        void fabricate(const FabricationRule& frule);
    };

    /* Implementation */

    inline bool WorkRule::accept_conj(const smtlit_t& l, const smtannotation_map& annots) const {
        for (const FabricationFilter& filter : filters)
            if (!filter.accept(l, annots))
                return false;
        return true;
    }

    inline bool WorkRule::accept_disj(const smtlit_t& l, const smtannotation_map& annots) const {
        for (const FabricationFilter& filter : filters)
            if (filter.accept(l, annots))
                return true;
        return false;
    }

    inline bool WorkRule::accept(const smtlit_t& l, const smtannotation_map& annots) const {
        if (mode == FilterMode::Conjunctive)
            return accept_conj(l, annots);
        else
            return accept_disj(l, annots);
    }

    inline const std::set<smtparam_size_t> FabricationRule::unbound() const {
        std::set<smtparam_size_t> res;
        for (smtparam_size_t p = 0; p < plist(fun).size(); ++p)
            res.insert(p);
        for (smtparam_binding b : default_binds)
            res.erase(b.first);
        return res;
    }

    inline void FabricationRule::update(smtparam_binding_set& binds) const {
        for (smtparam_binding bind : default_binds)
            binds.insert(bind);
    }

    inline smtlit_t FabricationRule::generate(const smtparam_binding_set& binds) const {
        return apply(fun, binds);
    }

    inline const std::set<smtlit_t>& SmtLitFabricator::filter(const FiltrationRule& frule, bool reset) {
        if (reset || filtered.empty()) {
            filtered.clear();
            for (const std::pair<smtident_t, smtlit_t>& lpair : lits) {
                const smtlit_t& l = lpair.second;
                if (frule.accept(l, _annots))
                    filtered.insert(l);
            }
        }
        return filtered;
    }

    inline void SmtLitFabricator::annotate(const smtident_t& l, const smtannotation_t& a) {
        _annots[a].insert(l);
    }
    inline void SmtFunStorage::annotate(const smtident_t& f, const smtannotation_t& a) {
        _annots[a].insert(f);
    }

    inline void SmtLitFabricator::insert(const smtlit_t& l) {
        lits[ident(l)] = l;
        _types[type(l)].insert(ident(l));
    }
    inline void SmtFunStorage::insert(const smtfun_t& f) {
        funs[ident(f)] = f;
        _types[rtype(f)].insert(ident(f));
    }

    inline void SmtLitFabricator::insert(const smtlit_t& l, const smtannotation_t& a) {
        insert(l);
        annotate(ident(l), a);
    }
    inline void SmtFunStorage::insert(const smtfun_t& f, const smtannotation_t& a) {
        insert(f);
        annotate(ident(f), a);
    }

}

#endif
