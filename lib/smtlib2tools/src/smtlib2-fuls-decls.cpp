#define LIB_SMTLIB2_CPP_TOOLS__FILEUTILS_EXTRACT_DECLS__CPP

#include <snlog/snlog.hpp>
#include <lisptp/lisptp.hpp>
#include <smtlib2tools/smtlib2-fileutils.hpp>

using namespace smtlib2;

struct Smt2DeclLTV : public lisptp::LispTreeVisitor<const std::string> {
    smtfile_decls& coredata;
    Smt2DeclLTV(smtfile_decls& coredata) : coredata(coredata) {}
protected:
    virtual const std::string handle_term(const std::string& t) const { return t; }
    virtual const std::string handle_call
    (const std::string& op, const std::vector<const std::string>& lvs) const {
        // TODO: check lvs accesses in range for readability of errors
        if (op == "declare-const") {
            coredata.add_symbol(lvs.front());
        } else if (op == "declare-fun") {
            coredata.add_symbol(lvs.front());
        } else if (op == "define-fun") {
            coredata.add_symbol(lvs.front());
        }
        // TODO: Add usual logics declarations (from the selogic I suppose)
        // TODO: Better decl tests (quatified vars, etc.)
        return "";
    }
};

extern const smtfile_decls smtlib2::extract_declarations(const std::string& filename) {
    auto fdata = lisptp::parse_file(filename);
    smtfile_decls coredata;
    Smt2DeclLTV visitor(coredata);
    visitor.visit(fdata);
    return coredata;
}
