#ifndef WHY3_WHYML_IPH_FOR_GPID__CONSTRAINT__HPP
#define WHY3_WHYML_IPH_FOR_GPID__CONSTRAINT__HPP

#include <string>

class Why3_Constraint {
    std::string _d;
public:
    Why3_Constraint() : _d("true") {}
    Why3_Constraint(const std::string& d) : _d(d) {}
    Why3_Constraint(const Why3_Constraint& o) : _d(o._d) {}
    inline const std::string str() const { return _d; }
    inline operator const std::string() const { return _d; }

    static inline Why3_Constraint disjunct(const Why3_Constraint& l, const Why3_Constraint& r)
    { return "(or " + l.str() + r.str() + ")"; }
};

#endif
