#define GPID_FRAMEWORK__UTIL__ABDPARSER_GENERIC_CPP

#include <snlog/snlog.hpp>
#include <stdutils/collections.hpp>
#include <abdulot/core/errors.hpp>
#include <abdulot/utils/abducibles-core.hpp>

using namespace snlog;
using namespace abdulot;

/* Keywords */

const std::string abdkw_size = "size";
const std::string abdkw_rsize = "rsize";
const std::string abdkw_abduce = "abduce";
const std::string abdkw_abducible = "abducible";
const std::string abdkw_reference = "reference";
const std::string abdkw_ref = "ref";
const std::string abdkw_extend = "extend";
const std::string abdkw_declare = "declare";
const std::string abdkw_lambda = "lambda";
const std::string abdkw_declare_lambda = "declare-lambda";
const std::string abdkw_apply = "apply";
const std::string abdkw_strict = "strict";
const std::string abdkw_as = "as";
const std::string abdkw_auto = "auto";
const std::string abdkw_over = "over";

const std::string abdkw_symmetric = "symmetric";

/* Lambda utils */

AbducibleParserVisitor::Lextender::Lextender
(const std::vector<std::string>& params, const std::string& extension)
{
    std::map<std::pair<size_t, size_t>, size_t> cuts;
    size_t ppos = 0;
    for (const std::string& param : params) {
        size_t lock = extension.find(param);
        while (lock != std::string::npos) {
            cuts[std::pair<size_t, size_t>(lock, param.length())] = ppos;
            lock = extension.find(param, lock+param.length());
        }
        ++ppos;
    }
    size_t lock = 0;
    size_t spos = 0;
    for (auto& cdata : cuts) {
        wires[cdata.second] = lock++;
        extparts.push_back(extension.substr(spos, cdata.first.first - spos));
        spos = cdata.first.first + cdata.first.second;
    }
    extparts.push_back(extension.substr(spos));
}

const std::string AbducibleParserVisitor::Lextender
::extend(const std::vector<std::string>& params) const {
    std::stringstream extended;
    for (size_t pos = 0; pos + 1 < extparts.size(); ++pos) {
        extended << extparts.at(pos) << params.at(wires.at(pos));
    }
    extended << extparts.back();
    return extended.str();
}

AbducibleParserVisitor::AbducibleLambda::AbducibleLambda
(const std::string& name, const std::vector<std::string>& params, const std::string& extension)
    : name(name), pcount(params.size()), extender(params, extension)
{}

static inline bool next
(std::vector<std::set<size_t>::iterator>& itparams,
 const std::vector<std::set<size_t>>& params) {
    size_t cpos = 0;
    while (cpos < itparams.size() && ++itparams.at(cpos) == params.at(cpos).end()) {
        itparams[cpos] = params.at(cpos).begin();
        ++cpos;
    }
    return cpos < itparams.size();
}

static inline bool option_check
(const std::vector<std::string>& values, const std::set<std::string>& options) {
    if (stdutils::inset(options, abdkw_symmetric)) {
        for (size_t p = 0; p + 1 < values.size(); ++p)
            if (values.at(p) >= values.at(p+1))
                return false;
    }
    // TODO: Handle more application options
    return true;
}

const std::set<std::string> AbducibleParserVisitor::AbducibleLambda::apply
(const std::vector<std::set<size_t>>& params,
 const std::vector<std::string>& decls,
 const std::set<std::string>& options) const {
    std::set<std::string> res;
    std::vector<std::set<size_t>::iterator> itparams;
    for (const std::set<size_t>& pset : params) itparams.push_back(pset.begin());
    do {
        std::vector<std::string> values;
        for (auto it : itparams) values.push_back(decls.at(*it));
        if (option_check(values, options))
            res.insert(extender.extend(values));
    } while (next(itparams, params));
    return res;
}

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
        if (nvalue == abdkw_size)
            handle_size(node);
        if (nvalue == abdkw_rsize)
            handle_rsize(node);
        if (nvalue == abdkw_abduce || nvalue == abdkw_abducible)
            handle_abducible(node);
        if (nvalue == abdkw_reference || nvalue == abdkw_ref)
            handle_reference(node);
        if (nvalue == abdkw_extend)
            handle_extend(node);
        if (nvalue == abdkw_declare)
            handle_declare(node);
        if (nvalue == abdkw_lambda || nvalue == abdkw_declare_lambda)
            handle_lambda(node);
        if (nvalue == abdkw_apply)
            handle_apply(node);
    } else {
        // We do not need to handle terms
    }
    handled = true;
}

void AbducibleParserVisitor::handle_size(const lisptp::LispTreeNode& node) {
    _ensure(node.getLeaves().size() == 1, "<size> command must have one (and only one) argument");
    auto data = (node.getLeaves().front())->getValue();
    if (data == abdkw_auto) {
        auto_size = true;
    } else {
        size = std::stoi(data);
        _ensure(size > 0, "forced abducible size must be > 0");
    }
}

void AbducibleParserVisitor::handle_rsize(const lisptp::LispTreeNode& node) {
    _ensure(node.getLeaves().size() == 1, "<rsize> command must have one (and only one) argument");
    auto data = (node.getLeaves().front())->getValue();
    if (data == abdkw_auto) {
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
        _ensure(!leaf->isCall(), "annotations must be non calls");
        for (size_t idx : annots.at(leaf->getValue()))
            abddata.push_back(decls.at(idx));
    }
}

void AbducibleParserVisitor::handle_declare(const lisptp::LispTreeNode& node) {
    std::set<size_t> adds;
    bool a_phase = false;
    for (auto leaf : node.getLeaves()) {
        if (a_phase) {
            _ensure(!leaf->isCall(), "annotations must be non calls");
            for (size_t alm : adds)
                annots[leaf->getValue()].insert(alm);
        } else if (!leaf->isCall() && leaf->getValue() == abdkw_as) {
            a_phase = true;
        } else {
            adds.insert(decls.size());
            decls.push_back(leaf->str(false));
        }
    }
}

void AbducibleParserVisitor::handle_lambda(const lisptp::LispTreeNode& node) {
    _ensure(node.getLeaves().size() == 3, "lambda decl is takes 3 parameters <name> <params> <extension>");
    auto lname_node = node.getLeaves().at(0);
    auto param_node = node.getLeaves().at(1);
    auto exten_node = node.getLeaves().at(2);
    _ensure(!lname_node->isCall(), "lambda name must be non-call");
    _ensure(param_node->isCall(), "wrong lambda parameters format");
    const std::string lname = lname_node->getValue();
    std::vector<std::string> params;
    params.push_back(param_node->getValue());
    for (auto pleaf : param_node->getLeaves()) {
        _ensure(!pleaf->isCall(), "param leaf must be annot-type");
        params.push_back(pleaf->getValue());
    }
    AbducibleLambda lambda(lname, params, exten_node->str(false));
    lambdas.emplace(lname, lambda);
}

void AbducibleParserVisitor::handle_apply(const lisptp::LispTreeNode& node) {
    _ensure(node.getLeaves().size() >= 3, "apply takes at least 3 pars <ref> <params> <target> <opts>*");
    auto lname_node = node.getLeaves().at(0);
    auto param_node = node.getLeaves().at(1);
    auto targt_node = node.getLeaves().at(2);
    _ensure(!lname_node->isCall(), "lambda name must be non-call");
    const std::string lname = lname_node->getValue();
    _ensure(param_node->isCall(), "wrong apply parameters format");
    std::vector<std::set<size_t>> params;
    _ensure(param_node->getValue() == abdkw_over, "wrong apply parameters format");
    for (auto pleaf : param_node->getLeaves()) {
        std::set<size_t> iset;
        if (!pleaf->isCall()) {
            for (size_t r : annots.at(pleaf->getValue())) {
                iset.insert(r);
            }
        } else if (pleaf->getValue() == abdkw_strict) {
            _ensure(pleaf->getLeaves().size() == 1, "strict definition must be singled");
            iset.insert(decls.size());
            decls.push_back(pleaf->getLeaves().front()->str(false));
        } else {
            _ensure(false, "unknown param type: " + pleaf->getValue());
        }
        params.push_back(iset);
    }
    _ensure(!targt_node->isCall(), "target name must be non-call");
    const std::string target = targt_node->getValue();
    std::set<std::string> options;
    for (size_t p = 3 ; p < node.getLeaves().size(); ++p) {
        _ensure(!node.getLeaves().at(p)->isCall(), "option name must be non-call");
        options.insert(node.getLeaves().at(p)->getValue());
    }
    _ensure(params.size() == lambdas.at(lname).get_pcount(), "incompatible param size");
    for (const std::string nabd : lambdas.at(lname).apply(params, decls, options)) {
        annots[target].insert(decls.size());
        decls.push_back(nabd);
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
