#ifndef WHY3_WHYML_ICH_FOR_GPID__CONSTRAINT__HPP
#define WHY3_WHYML_ICH_FOR_GPID__CONSTRAINT__HPP

#include <string>

namespace gpid {

    class W3WML_Constraint {
        std::string _d;
    public:
        W3WML_Constraint() : _d("true") {}
        W3WML_Constraint(const std::string& d) : _d(d) {}
        W3WML_Constraint(const W3WML_Constraint& o) : _d(o._d) {}
        inline const std::string str() const { return _d; }
        inline operator const std::string() const { return _d; }

        static inline W3WML_Constraint disjunct(const W3WML_Constraint& l, const W3WML_Constraint& r)
        { return "(" + l.str() + ") \\/ (" + r.str() + ")"; }
    };

}

#endif
