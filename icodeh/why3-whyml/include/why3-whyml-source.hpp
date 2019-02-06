#ifndef WHY3_WHYML_ICH_FOR_GPID__SOURCE__HPP
#define WHY3_WHYML_ICH_FOR_GPID__SOURCE__HPP

#include <map>
#include <set>
#include <list>
#include <memory>
#include "why3-whyml-constraint.hpp"

class W3WML_Template {
public:
    struct Element {
        enum class ElemType { Code, Invariant };
        const ElemType type;
        virtual ~Element() = default;
    protected:
        Element(ElemType t) : type(t) {}
    };
    using ElementPtr = std::shared_ptr<Element>;

    struct CodeElement : public Element {
        const std::string data;
        CodeElement(const std::string& d) : Element(ElemType::Code), data(d) {}
    };

    struct InvariantElement : public Element {
        std::list<const std::string> conj;
        InvariantElement() : Element(ElemType::Invariant) {}
    };
private:
    std::map<size_t, ElementPtr> elements;
    std::set<size_t> invariant_ids;
public:
    W3WML_Template(const std::string& filename);

    inline const std::map<size_t, ElementPtr>& getElements() const { return elements; }
    inline const std::set<size_t>& getInvariantIds() const { return invariant_ids; }

    inline Element& getElement(size_t idx) const
    { return *(elements.at(idx)); }

    inline CodeElement& getCode(size_t idx) const
    { return *(std::dynamic_pointer_cast<CodeElement>(elements.at(idx))); }
    inline InvariantElement& getInvariant(size_t idx) const
    { return *(std::dynamic_pointer_cast<InvariantElement>(elements.at(idx))); }

    void save_to(const std::string& filename, const std::set<std::string>& refs) const;
};

inline std::ostream& operator<<(std::ostream& out, const W3WML_Template::CodeElement& e) {
    return out << e.data;
}

std::ostream& write(std::ostream& out, const W3WML_Template::InvariantElement& e,
                    const std::set<std::string>& refs);

inline std::ostream& write(std::ostream& out, const W3WML_Template::ElementPtr e,
                           const std::set<std::string>& refs) {
    if (e->type == W3WML_Template::Element::ElemType::Code)
        return out << *std::dynamic_pointer_cast<W3WML_Template::CodeElement>(e);
    else
        return write(out, *std::dynamic_pointer_cast<W3WML_Template::InvariantElement>(e), refs);
}

inline std::ostream& write(std::ostream& out, const W3WML_Template& t,
                           const std::set<std::string>& refs) {
    for (auto e : t.getElements()) write(out, e.second, refs);
    return out;
}

class W3WML_LSet {
    std::list<std::string> literals;
    std::set<std::string> references;
public:
    W3WML_LSet(const std::string& filename, bool overriden);
    inline const std::list<std::string>& getLiterals() const { return literals; }
    inline const std::set<std::string>& getReferences() const { return references; }
};

#endif
