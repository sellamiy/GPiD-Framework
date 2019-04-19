#ifndef WHY3_WHYML_IPH_FOR_GPID__SOURCE__HPP
#define WHY3_WHYML_IPH_FOR_GPID__SOURCE__HPP

#include <why3cpp/why3proof.hpp>
#include <why3cpp/why3utils.hpp>
#include "why3-constraint-wrapper.hpp"

class Why3_Template {
public:
    struct Element {
        enum class ElemType { Raw, Property };
        const ElemType type;
        virtual ~Element() = default;
    protected:
        Element(ElemType t) : type(t) {}
    };
    using ElementPtr = std::shared_ptr<Element>;

    struct RawElement : public Element {
        const std::string data;
        RawElement(const std::string& d) : Element(ElemType::Raw), data(d) {}
    };

    struct PropertyElement : public Element {
        std::vector<std::string> conj;
        const std::string type;
        PropertyElement(const std::string& type) : Element(ElemType::Property), type(type) {}
        PropertyElement(const std::string& type, const std::vector<std::string>& conj)
            : Element(ElemType::Property), conj(conj), type(type) {}
    };
private:
    std::map<size_t, ElementPtr> elements;
    std::set<size_t> prop_ids;
public:
    Why3_Template(const std::string& filename);
    Why3_Template(const Why3_Template& source);

    inline const std::map<size_t, ElementPtr>& getElements() const { return elements; }
    inline const std::set<size_t>& getPropertyIds() const { return prop_ids; }

    inline Element& getElement(size_t idx) const
    { return *(elements.at(idx)); }

    inline RawElement& getSource(size_t idx) const
    { return *(std::dynamic_pointer_cast<RawElement>(elements.at(idx))); }
    inline PropertyElement& getProperty(size_t idx) const
    { return *(std::dynamic_pointer_cast<PropertyElement>(elements.at(idx))); }

    void save_to(const std::string& filename, const why3cpp::Why3ConvertMap& cmap) const;
};

inline std::ostream& operator<<(std::ostream& out, const Why3_Template::RawElement& e) {
    return out << e.data;
}

std::ostream& write
(std::ostream& out, const Why3_Template::PropertyElement& e, const why3cpp::Why3ConvertMap& cmap);

inline std::ostream& write
(std::ostream& out, const Why3_Template::ElementPtr e, const why3cpp::Why3ConvertMap& cmap) {
    if (e->type == Why3_Template::Element::ElemType::Raw)
        return out << *std::dynamic_pointer_cast<Why3_Template::RawElement>(e);
    else
        return write(out, *std::dynamic_pointer_cast<Why3_Template::PropertyElement>(e), cmap);
}

inline std::ostream& write
(std::ostream& out, const Why3_Template& t, const why3cpp::Why3ConvertMap& cmap) {
    for (auto e : t.getElements()) write(out, e.second, cmap);
    return out;
}

#endif
