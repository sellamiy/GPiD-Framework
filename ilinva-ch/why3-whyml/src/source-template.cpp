#define WHY3_WHYML_ICH_FOR_GPID__SOURCE__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <why3wrap/why3wrap.hpp>
#include <smtlit/smtlit.hpp>
#include <gpid/core/errors.hpp>
#include <why3-whyml-source.hpp>

using namespace gpid;

void W3WML_Template::save_to(const std::string& filename, const std::set<std::string>& refs) const {
    std::ofstream ofs(filename);
    if (!ofs.is_open())
        throw InternalError("W3WML_Template could not open tempfile");
    write(ofs, *this, refs);
    ofs.close();
}

std::ostream& gpid::write(std::ostream& out, const W3WML_Template::InvariantElement& e,
                          const std::set<std::string>& refs) {
    out << "invariant {";
    if (e.conj.empty()) {
        out << " true ";
    } else {
        bool start = true;
        for (auto s : e.conj) {
            if (start) start = false;
            else out << " /\\ ";
            out << "(" << why3wrap::Smt2Why3(s, refs) << ")";
        }
    }
    return out << "}";
}

struct W3WML_LSet_LRec {
    std::list<std::string>& llist;
    W3WML_LSet_LRec(std::list<std::string>& llist) : llist(llist) {}
    inline void handle(const std::string lit) { llist.push_back(lit); }
};

W3WML_LSet::W3WML_LSet(const std::string& filename) {
    try {
        smtlit::GenerationSet gset =
            smtlit::generate_literals
            <smtlit::GenerationSource::File, smtlit::GenerationPreset::WhyML>
            (filename);
        for (const smtlit::smtlit_t& lit : gset.get_literals())
            literals.push_back(smtlit::ident(lit));
        references = gset.get_annotated(smtlit::annot_whyml_ref);
    } catch (gpid::GPiDError& e) {
        snlog::l_error() << "W3WML Mlw literals recovery failed: " << e.what() << snlog::l_end;
    }
}
