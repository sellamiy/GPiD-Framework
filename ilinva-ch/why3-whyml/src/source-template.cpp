#define WHY3_WHYML_ICH_FOR_GPID__SOURCE__CPP

#include <fstream>
#include <snlog/snlog.hpp>
#include <gpid/core/errors.hpp>
#include <gpid/masmalig/algorithm.hpp>
#include <why3-whyml-source.hpp>

using namespace gpid;

void W3WML_Template::save_to(const std::string& filename) const {
    std::ofstream ofs(filename);
    if (!ofs.is_open())
        throw InternalError("W3WML_Template could not open tempfile");
    ofs << *this;
    ofs.close();
}

std::ostream& gpid::operator<<(std::ostream& out, const W3WML_Template::InvariantElement& e) {
    out << "invariant {";
    if (e.conj.empty()) {
        out << " true ";
    } else {
        bool start = true;
        for (auto s : e.conj) {
            if (start) start = false;
            else out << " /\\ ";
            out << "(" << s << ")";
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
        GPiDOptions opts;
        MasmaligOptions mopts;
        mopts.whyml_files.push_back(filename);
        W3WML_LSet_LRec handler(literals);
        MasmaligAlgorithm<W3WML_LSet_LRec> loader(handler, opts, mopts);
        loader.execute();
        references = loader.getBuilder().getWhyMLRefs();
    } catch (mlbsmt2::MLB2Error& e) {
        snlog::l_error() << "W3WML Mlw literals recovery failed: " << e.what() << snlog::l_end;
    } catch (gpid::GPiDError& e) {
        snlog::l_error() << "W3WML Mlw literals recovery failed: " << e.what() << snlog::l_end;
    }
}
