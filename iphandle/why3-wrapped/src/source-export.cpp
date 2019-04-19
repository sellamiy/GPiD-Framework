#define WHY3_WHYML_IPH_FOR_GPID__SOURCE__CPP

#include <fstream>
#include <stdutils/random.hpp>
#include <smtlib2tools/literal-presets.hpp>
#include <why3cpp/whyml-smtlit.hpp>
#include <abdulot/core/errors.hpp>
#include <why3-content-wrapper.hpp>
#include <why3-lset-wrapper.hpp>

void Why3_Template::save_to(const std::string& filename, const why3cpp::Why3ConvertMap& cmap) const {
    std::ofstream ofs(filename);
    if (!ofs.is_open())
        throw abdulot::InternalError("Why3_Template could not open tempfile");
    write(ofs, *this, cmap);
    ofs.close();
}

std::ostream& write
(std::ostream& out, const Why3_Template::PropertyElement& e, const why3cpp::Why3ConvertMap& cmap) {
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

struct Why3_LSet_LRec {
    std::vector<std::string>& llist;
    Why3_LSet_LRec(std::vector<std::string>& llist) : llist(llist) {}
    inline void handle(const std::string lit) { llist.push_back(lit); }
};

Why3_LSet::Why3_LSet
(const std::string& filename, const why3cpp::Why3ConvertMap& cmap, bool overriden, bool shuffle) {
    if (overriden)
        // We do not need to generate abduction literals if we load them
        return;
    try {
        smtlib2::GenerationSet gset =
            why3cpp::generate_literals_whyml(filename);
        for (const smtlib2::smtlit_t& lit : gset.get_literals())
            literals.push_back(why3cpp::SmtBackwardConvert(smtlib2::ident(lit), cmap));
        references = gset.get_annotated(why3cpp::annot_whyml_ref);
    } catch (abdulot::CoreError& e) {
        snlog::l_error() << "Why3 Mlw literals recovery failed: " << e.what() << snlog::l_end;
    }
    if (shuffle)
        stdutils::shuffle(literals);
}
