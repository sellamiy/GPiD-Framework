#ifndef LIB_SMTLIB2_CPP_TOOLS__CORE__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__CORE__HEADER

#include <set>
#include <map>
#include <tuple>
#include <vector>
#include <string>

namespace smtlib2 {

    using smtident_t = std::string;
    using smttype_t = std::string;
    using smtannotation_t = std::string;

    using smtlit_t = std::pair<smtident_t, smttype_t>;
    using smtlit_set = std::map<smtident_t, smtlit_t>;

    using smtparam_size_t = uint32_t;
    using smtfun_t = std::tuple<smtident_t, smttype_t, std::vector<smttype_t>>;
    using smtfun_set = std::map<smtident_t, smtfun_t>;

    using smttype_map = std::map<smttype_t, std::set<smtident_t>>;
    using smtannotation_map = std::map<smtannotation_t, std::set<smtident_t>>;

    using smtparam_binding = std::pair<smtparam_size_t, smtident_t>;
    using smtparam_binding_set = std::map<smtparam_size_t, smtident_t>;

    using param_iterator = std::tuple<smtparam_size_t, smttype_t, std::set<smtident_t>::const_iterator>;
    using param_iterator_set = std::vector<param_iterator>;

    static inline const smtident_t& ident(const smtlit_t& l) { return l.first; }
    static inline const smtident_t& ident(const smtfun_t& f) { return std::get<0>(f); }

    static inline const smtident_t& ident(const smtparam_binding& b) { return b.second; }

    static inline const smttype_t& type(const smtlit_t& l) { return l.second; }
    static inline const smttype_t& rtype(const smtfun_t& f) { return std::get<1>(f); }

    static inline const smtident_t& ident(const param_iterator& pit) { return *std::get<2>(pit); }
    static inline const smttype_t& type(const param_iterator& pit) { return std::get<1>(pit); }
    static inline smtparam_size_t binder(const param_iterator& pit) { return std::get<0>(pit); }
    static inline std::set<smtident_t>::const_iterator& iterator(param_iterator& pit)
    { return std::get<2>(pit); }

    static inline const std::vector<smttype_t>& plist(const smtfun_t& f) { return std::get<2>(f); }

    extern const smtannotation_t annotation(const smtident_t& i, const smtannotation_map& am);

    extern smtlit_t apply(const smtfun_t& f, const smtparam_binding_set& params);

    extern bool is_reserved(const smtident_t& ident);

    extern bool is_literal(const smtident_t& ident);

}

#endif
