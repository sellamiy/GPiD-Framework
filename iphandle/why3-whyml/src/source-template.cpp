#define WHY3_WHYML_IPH_FOR_GPID__SOURCE__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <why3cpp/why3cpp.hpp>
#include <smtlib2tools/smtlit-presets.hpp>
#include <abdulot/core/errors.hpp>
#include <why3-whyml-source.hpp>

void W3WML_Template::save_to(const std::string& filename, const why3cpp::Why3ConvertMap& cmap) const {
    std::ofstream ofs(filename);
    if (!ofs.is_open())
        throw abdulot::InternalError("W3WML_Template could not open tempfile");
    write(ofs, *this, cmap);
    ofs.close();
}

std::ostream& write
(std::ostream& out, const W3WML_Template::PropertyElement& e, const why3cpp::Why3ConvertMap& cmap) {
    out << e.type << " {";
    if (e.conj.empty()) {
        out << " true ";
    } else {
        bool start = true;
        for (auto s : e.conj) {
            if (start) start = false;
            else out << " /\\ ";
            out << "(" << why3cpp::Smt2Why3(s, cmap) << ")";
        }
    }
    return out << "}";
}

struct W3WML_LSet_LRec {
    std::list<std::string>& llist;
    W3WML_LSet_LRec(std::list<std::string>& llist) : llist(llist) {}
    inline void handle(const std::string lit) { llist.push_back(lit); }
};

W3WML_LSet::W3WML_LSet(const std::string& filename, bool overriden) {
    if (overriden)
        // We do not need to generate abduction literals if we load them
        return;
    try {
        smtlib2::GenerationSet gset =
            why3cpp::generate_literals_whyml(filename);
        for (const smtlib2::smtlit_t& lit : gset.get_literals())
            literals.push_back(smtlib2::ident(lit));
        references = gset.get_annotated(why3cpp::annot_whyml_ref);
    } catch (abdulot::CoreError& e) {
        snlog::l_error() << "W3WML Mlw literals recovery failed: " << e.what() << snlog::l_end;
    }
}
