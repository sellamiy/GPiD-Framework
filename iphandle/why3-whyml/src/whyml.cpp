#define WHY3_WHYML_IPH_FOR_GPID__WHYML_HANDLER__CPP

#include <fstream>
#include <abdulot/core/errors.hpp>
#include <why3-whyml-source.hpp>

W3WML_Template::W3WML_Template(const std::string& filename) {
    std::ifstream ifs(filename);
    std::string line;
    std::stringstream buf;
    size_t cid = 0;

    if (!ifs.is_open())
        throw abdulot::DataError("Problem file not found: " + filename);

    while (getline(ifs, line)) {
        if (size_t loc = line.find("invariant") != std::string::npos) {
            buf << line.substr(0, loc);
            elements[cid++] = ElementPtr(new RawElement(buf.str()));
            prop_ids.insert(cid);
            elements[cid++] = ElementPtr(new PropertyElement("invariant"));
            buf.str(std::string());
            loc = line.find("}", loc);
            buf << line.substr(loc + 1) << '\n';
        } else {
            buf << line << '\n';
        }
    }
    elements[cid++] = ElementPtr(new RawElement(buf.str()));
    ifs.close();
}

W3WML_Template::W3WML_Template(const W3WML_Template& source) : prop_ids(source.prop_ids) {
    /* This perform content copy of current property strengthenings, not linked to the original */
    for (const auto& element : source.elements) {
        if (stdutils::inset(prop_ids, element.first)) {
            const PropertyElement& pel = *(std::dynamic_pointer_cast<PropertyElement>(element.second));
            elements[element.first] = ElementPtr(new PropertyElement(pel.type, pel.conj));
        } else {
            elements.insert(element);
        }
    }
}
