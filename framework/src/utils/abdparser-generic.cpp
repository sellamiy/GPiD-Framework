#define GPID_FRAMEWORK__UTIL__ABDPARSER_GENERIC_CPP

#include <snlog/snlog.hpp>
#include <abdulot/core/errors.hpp>
#include <abdulot/utils/abducibles-core.hpp>

using namespace snlog;
using namespace abdulot;

/* Command handlers utils */

void AbducibleParserVisitor::_ensure(bool b, const std::string& msg) {
    if (!b) {
        snlog::l_error() << "Abducible file contextual error: " << msg << snlog::l_end;
        valid = false;
    }
}

void AbducibleParserVisitor::handle(const lisptp::LispTreeNode& node) {
    if (node.isCall()) {
        const std::string& nvalue = node.getValue();
        if (nvalue == "") {
            // Multiple lisp-tree et top level
            for (auto leaf : node.getLeaves())
                handle(*leaf);
        }
        if (nvalue == "size")
            handle_size(node);
        if (nvalue == "rsize")
            handle_rsize(node);
        if (nvalue == "abduce" || nvalue == "abducible")
            handle_abducible(node);
        if (nvalue == "reference" || nvalue == "ref")
            handle_reference(node);
        if (nvalue == "extend")
            handle_extend(node);
        if (nvalue == "declare")
            handle_declare(node);
    } else {
        // We do not need to handle terms
    }
    handled = true;
}

void AbducibleParserVisitor::handle_size(const lisptp::LispTreeNode& node) {
    _ensure(node.getLeaves().size() == 1, "<size> command must have one (and only one) argument");
    auto data = (node.getLeaves().front())->getValue();
    if (data == "auto") {
        auto_size = true;
    } else {
        size = std::stoi(data);
        _ensure(size > 0, "forced abducible size must be > 0");
    }
}

void AbducibleParserVisitor::handle_rsize(const lisptp::LispTreeNode& node) {
    _ensure(node.getLeaves().size() == 1, "<rsize> command must have one (and only one) argument");
    auto data = (node.getLeaves().front())->getValue();
    if (data == "auto") {
        auto_size = true;
    } else {
        rsize = std::stoi(data);
    }
}

void AbducibleParserVisitor::handle_abducible(const lisptp::LispTreeNode& node) {
    for (auto leaf : node.getLeaves())
        abddata.push_back(leaf->str(false));
}

void AbducibleParserVisitor::handle_reference(const lisptp::LispTreeNode& node) {
    for (auto leaf : node.getLeaves())
        refdata.push_back(leaf->str(false));
}

void AbducibleParserVisitor::handle_extend(const lisptp::LispTreeNode& node) {
    for (auto leaf : node.getLeaves()) {
        _ensure(!leaf->isCall(), "Annotations must be non calls");
        for (size_t idx : annots.at(leaf->getValue()))
            abddata.push_back(decls.at(idx));
    }
}

void AbducibleParserVisitor::handle_declare(const lisptp::LispTreeNode& node) {
    std::set<size_t> adds;
    bool a_phase = false;
    for (auto leaf : node.getLeaves()) {
        if (a_phase) {
            _ensure(!leaf->isCall(), "Annotations must be non calls");
            for (size_t alm : adds)
                annots[leaf->getValue()].insert(alm);
        } else if (!leaf->isCall() && leaf->getValue() == "as") {
            a_phase = true;
        } else {
            adds.insert(decls.size());
            decls.push_back(leaf->str(false));
        }
    }
}

uint32_t AbducibleParserVisitor::getSize() {
    return auto_size ? abddata.size() : size;
}

uint32_t AbducibleParserVisitor::getRefCount() {
    return auto_size ? refdata.size() : rsize;
}

const std::string& AbducibleParserVisitor::nextAbducible() {
    if (!ait_init) {
        abdit = abddata.begin();
        ait_init = true;
    }
    if (abdit == abddata.end()) {
        snlog::l_info()
            << "The following may be triggered by wrong size information in abducible file"
            << snlog::l_end
            << snlog::l_info
            << "The following may be an internal error"
            << snlog::l_end;
        throw IllegalAccessError("No more abducible literal");
    }
    const std::string& res = *abdit;
    ++abdit;
    return res;
}

const std::string& AbducibleParserVisitor::nextReference() {
    if (!rit_init) {
        refit = refdata.begin();
        rit_init = true;
    }
    if (refit == refdata.end()) {
        snlog::l_info()
            << "The following may be triggered by wrong size information in abducible file"
            << snlog::l_end
            << snlog::l_info
            << "The following may be an internal error"
            << snlog::l_end;
        throw IllegalAccessError("No more reference literal");
    }
    const std::string& res = *refit;
    ++refit;
    return res;
}

/* Parser engine utils */

AbducibleParser::AbducibleParser(const std::string& filename) {
    pdata = lisptp::parse_file(filename);
}

uint32_t AbducibleParser::getAbducibleCount() {
    if (!pvisitor.isComplete())
        pvisitor.handle(*pdata);
    return pvisitor.getSize();
}

uint32_t AbducibleParser::getReferenceCount() {
    if (!pvisitor.isComplete())
        pvisitor.handle(*pdata);
    return pvisitor.getRefCount();
}

const std::string& AbducibleParser::nextAbducible() {
    if (!pvisitor.isComplete())
        pvisitor.handle(*pdata);
    return pvisitor.nextAbducible();
}

const std::string& AbducibleParser::nextReference() {
    if (!pvisitor.isComplete())
        pvisitor.handle(*pdata);
    return pvisitor.nextReference();
}
