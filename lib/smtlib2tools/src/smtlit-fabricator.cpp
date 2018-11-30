#define LIB_SMTLIB2_CPP_TOOLS__FABRICATOR__CPP

#include <snlog/snlog.hpp>
#include <smtlib2tools/smtlib2-types.hpp>
#include <smtlib2tools/smtlit-fabricator.hpp>

using namespace smtlib2;

bool FabricationFilter::accept(const smtlit_t& l, const smtannotation_map& annots) const {
    switch (policy) {
    case FilterPolicy::Type_Include:
        return type(l) == data;
    case FilterPolicy::Type_Exclude:
        return type(l) != data;
    case FilterPolicy::Annotation_Include:
        return annots.count(data) > 0 && annots.at(data).count(ident(l)) > 0;
    case FilterPolicy::Annotation_Exclude:
        return annots.count(data) == 0 || annots.at(data).count(ident(l)) == 0;
    case FilterPolicy::Content_Include:
        return ident(l).find(data) != std::string::npos;
    case FilterPolicy::Content_Exclude:
        return ident(l).find(data) == std::string::npos;
    default:
        snlog::l_internal() << "Filter policy switch failure" << snlog::l_end;
        return false;
    }
}

bool FabricationRule::valid(param_iterator_set& pset, const smttype_map& src) const {
    if (pset.size() == 0)
        return false;
    return iterator(pset.at(0)) != src.at(type(pset.at(0))).cend();
}

void FabricationRule::next(param_iterator_set& pset, const smttype_map& src) const {
    if (pset.size() == 0)
        return;
    size_t vidx = pset.size() - 1;
    ++(iterator(pset.at(vidx)));
    while (vidx > 0 && (iterator(pset.at(vidx))) == src.at(type(pset.at(vidx))).cend()) {
        std::get<2>(pset.at(vidx)) = src.at(type(pset.at(vidx))).cbegin();
        --vidx;
        ++(iterator(pset.at(vidx)));
    }
}

bool FabricationRule::accept_bind(param_iterator_set& pset, const smtannotation_map& annots) const {
    if (policy == FabricationPolicy::Apply_Symmetric) {
        // TODO: More rejection Stuff
        snlog::l_warn() << "Not implemented @" << __FILE__ << ":" << __LINE__ << snlog::l_end;
        // Prereject
        /*
        for (size_t vidx = 0; vidx + 1 < pset.size(); ++vidx)
            if (pset.at(vidx).second >= pset.at(vidx + 1).second)
                return false;
        */
    }

    for (const param_iterator& pit : pset)
        if (!accept(smtlit_t(ident(pit), smt_anytype), annots))
            return false;
    return true;
}

smtparam_binding_set FabricationRule::
select(param_iterator_set& pset, const smttype_map& src, const smtannotation_map& annots) const {
    smtparam_binding_set res;
    while (valid(pset, src)) {
        if (accept_bind(pset, annots)) {
            for (const param_iterator& param : pset)
                res[binder(param)] = ident(param);
            next(pset, src);
            break;
        }
        next(pset, src);
    }
    return res;
}

void SmtLitFabricator::fabricate(const FabricationRule& frule) {
    std::set<smtlit_t> fabricated;
    const std::set<smtparam_size_t> unbounded = frule.unbound();
    param_iterator_set itmap;
    for (smtparam_size_t binder : unbounded) {
        const smttype_t& param_type = plist(frule.get_fun()).at(binder);
        itmap.push_back(param_iterator(binder, param_type, _types.at(param_type).cbegin()));
    }
    smtparam_binding_set nbinders = frule.select(itmap, _types, _annots);
    while (!nbinders.empty()) {
        frule.update(nbinders);
        fabricated.insert(frule.generate(nbinders));
        nbinders = frule.select(itmap, _types, _annots);
    }
    for (const smtlit_t& l : fabricated) {
        insert(l, frule.get_annotation());
    }
}
