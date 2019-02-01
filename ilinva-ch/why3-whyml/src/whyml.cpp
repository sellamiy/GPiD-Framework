#define WHY3_WHYML_ICH_FOR_GPID__WHYML_HANDLER__CPP

#include <fstream>
#include <sstream>
#include <abdulot/core/errors.hpp>
#include <why3-whyml-source.hpp>

using namespace gpid;

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
            elements[cid++] = ElementPtr(new CodeElement(buf.str()));
            invariant_ids.insert(cid);
            elements[cid++] = ElementPtr(new InvariantElement());
            buf.str(std::string());
            loc = line.find("}", loc);
            buf << line.substr(loc + 1) << '\n';
        } else {
            buf << line << '\n';
        }
    }
    elements[cid++] = ElementPtr(new CodeElement(buf.str()));
    ifs.close();
}
