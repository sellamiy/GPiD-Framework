#include <iostream>
#include <sstream>
#include <stack>
#include <cstdio>
#include <cstring>
#include <array>
#include <snlog/snlog.hpp>
#include <stdutils/strings.hpp>
#include <stdutils/collections.hpp>
#include <lisptp/lisptp.hpp>
#include <context.hpp>
#include <solver-config.hpp>

#define CONTEXT_SL_CONSTRUCT_SRC

using namespace CVC4;
using namespace stdutils;
using namespace minpart;
using namespace minpart::slcvc;

const PartitionGeneratorOptions SLProblemContext::generate_partition_options() const {
    PartitionGeneratorOptions
        result(opts.c_blocksize, opts.c_depth, opts.p_blocksize, opts.p_depth,
               true, opts.random);
    return result;
}

static const std::string SL_SP_TRUE_KW  = "true";
static const std::string SL_SP_FALSE_KW = "false";

static const std::string SL_SP_AND_KW   = "and";
static const std::string SL_SP_OR_KW    = "or";
static const std::string SL_SP_NOT_KW   = "not";
static const std::string SL_SP_EQ_KW    = "=";
static const std::string SL_SP_NEQ_KW   = "distinct";
static const std::string SL_SP_PTO_KW   = "pto";
static const std::string SL_SP_EMP_KW   = "emp";
static const std::string SL_SP_SEP_KW   = "sep";
static const std::string SL_SP_WAND_KW  = "wand";

static const std::string SL_PBL_CMD_SORT_DECL  = "declare-sort";
static const std::string SL_PBL_CMD_CONST_DECL = "declare-const";
static const std::string SL_PBL_CMD_ASSERT     = "assert";

class SLProblemVisitor {
    ExprManager& em;
    Type integerType;
    bool valid;

    std::map<std::string, Type> sort_map;
    std::map<std::string, Expr> const_map;
    std::vector<Expr> asserts;

    void _ensure(bool b, const std::string& msg) {
        if (!b) {
            snlog::l_error() << "SL problem contextual error: " << msg << snlog::l_end;
            valid = false;
        }
    }

    void handle_sort_decl(const lisptp::LispTreeNode& node) {
        _ensure(node.getLeaves().size() == 2, "sort decl takes 2 parameters <name> <type>");
        auto sname_node = node.getLeaves().at(0);
        _ensure(!sname_node->isCall(), "sort name must be non-call");
        const std::string sname = sname_node->getValue();
        sort_map.emplace(sname, em.mkSetType(integerType));
    }

    void handle_const_decl(const lisptp::LispTreeNode& node) {
        _ensure(node.getLeaves().size() == 2, "vcst decl takes 2 parameters <name> <type>");
        auto cname_node = node.getLeaves().at(0);
        auto ctype_node = node.getLeaves().at(1);
        _ensure(!cname_node->isCall(), "const name must be non-call");
        _ensure(!ctype_node->isCall(), "const type must be non-call");
        const std::string cname = cname_node->getValue();
        const std::string ctype = ctype_node->getValue();
        const_map.emplace(cname, em.mkVar(cname, sort_map.at(ctype)));
    }

    inline void handle_assert(const lisptp::LispTreeNode& node) {
        _ensure(node.getLeaves().size() == 1, "assertions must have 1 param only");
        asserts.push_back(build_expr(*(node.getLeaves().at(0))));
    }

    Expr build_expr(const lisptp::LispTreeNode& node) {
        if (!node.isCall()) {
            if (node.getValue() == SL_SP_TRUE_KW) {
                return em.mkConst(true);
            } else if (node.getValue() == SL_SP_FALSE_KW) {
                return em.mkConst(false);
            } else if (stdutils::inmap(const_map, node.getValue())) {
                return const_map.at(node.getValue());
            } else {
                snlog::l_error() << "Unknown const in expr: " << node.getValue() << snlog::l_end;
                valid = false;
            }
        } else {
            if (node.getValue() == SL_SP_AND_KW) {
                _ensure(node.getLeaves().size() > 1, "and calls at least 2 params");
                Expr conj = build_expr(*(node.getLeaves().at(0)));
                bool first = true;
                for (auto leaf : node.getLeaves()) {
                    if (first) { first = false; } else {
                        conj = em.mkExpr(kind::AND, conj, build_expr(*leaf));
                    }
                }
                return conj;
            } else if (node.getValue() == SL_SP_OR_KW) {
                _ensure(node.getLeaves().size() > 1, "or calls at least 2 params");
                Expr disj = build_expr(*(node.getLeaves().at(0)));
                bool first = true;
                for (auto leaf : node.getLeaves()) {
                    if (first) { first = false; } else {
                        disj = em.mkExpr(kind::OR, disj, build_expr(*leaf));
                    }
                }
                return disj;
            } else if (node.getValue() == SL_SP_NOT_KW) {
                _ensure(node.getLeaves().size() == 1, "not calls exactly 1 param");
                return em.mkExpr(kind::NOT, build_expr(*(node.getLeaves().at(0))));
            } else if (node.getValue() == SL_SP_EQ_KW) {
                _ensure(node.getLeaves().size() == 2, "eq calls exactly 2 params");
                return em.mkExpr(kind::EQUAL, build_expr(*(node.getLeaves().at(0))),
                                 build_expr(*(node.getLeaves().at(1))));
            } else if (node.getValue() == SL_SP_NEQ_KW) {
                _ensure(node.getLeaves().size() == 2, "neq calls exactly 2 params");
                return em.mkExpr(kind::DISTINCT, build_expr(*(node.getLeaves().at(0))),
                                 build_expr(*(node.getLeaves().at(1))));
            } else if (node.getValue() == SL_SP_PTO_KW) {
                _ensure(node.getLeaves().size() == 2, "pto and calls exactly 2 params");
                return em.mkExpr(kind::SEP_PTO, build_expr(*(node.getLeaves().at(0))),
                                 build_expr(*(node.getLeaves().at(1))));
            } else if (node.getValue() == SL_SP_EMP_KW) {
                _ensure(node.getLeaves().size() == 2, "emp calls exactly 2 params");
                return em.mkExpr(kind::SEP_EMP, build_expr(*(node.getLeaves().at(0))),
                                 build_expr(*(node.getLeaves().at(1))));
            } else if (node.getValue() == SL_SP_SEP_KW) {
                _ensure(node.getLeaves().size() > 1, "sep calls at least 2 params");
                Expr conj = build_expr(*(node.getLeaves().at(0)));
                bool first = true;
                for (auto leaf : node.getLeaves()) {
                    if (first) { first = false; } else {
                        conj = em.mkExpr(kind::SEP_STAR, conj, build_expr(*leaf));
                    }
                }
                return conj;
            } else if (node.getValue() == SL_SP_WAND_KW) {
                _ensure(node.getLeaves().size() == 2, "wand calls exactly 2 params");
                return em.mkExpr(kind::SEP_WAND, build_expr(*(node.getLeaves().at(0))),
                                 build_expr(*(node.getLeaves().at(1))));
            } else {
                snlog::l_error() << "Unknown call in expr: " << node.getValue() << snlog::l_end;
                valid = false;
            }
        }
        return em.mkConst(false); // Error case
    }

public:

    SLProblemVisitor(ExprManager& em)
        : em(em), integerType(em.integerType()), valid(true) {}

    inline bool is_valid() const { return valid; }

    inline const std::map<std::string, Type>& get_sort_map() const { return sort_map; }
    inline const std::map<std::string, Expr>& get_const_map() const { return const_map; }
    inline const std::vector<Expr>& get_asserts() const { return asserts; }
    inline Expr get_formula() {
        return asserts.size() == 0 ? em.mkConst(true)
            : asserts.size() == 1 ? asserts.at(0)
            : em.mkExpr(kind::AND, asserts);
    }

    void handle(const lisptp::LispTreeNode& node) {
        if (node.isCall()) {
            const std::string& nvalue = node.getValue();
            if (nvalue == "") {
                // Multiple lisp-tree et top level
                for (auto leaf : node.getLeaves())
                    handle(*leaf);
            }
            if (nvalue == SL_PBL_CMD_SORT_DECL)
                handle_sort_decl(node);
            if (nvalue == SL_PBL_CMD_CONST_DECL)
                handle_const_decl(node);
            if (nvalue == SL_PBL_CMD_ASSERT)
                handle_assert(node);
        } else {
            // We do not need to handle terms
        }
    }

};

static const std::string SL_MDL_PART_MODEL = "model";
static const std::string SL_MDL_PART_HEAP  = "heap";

static const std::string SL_MDL_PMDL_SORT = "declare-sort";
static const std::string SL_MDL_PMDL_FUN  = "define-fun";

class SLModelVisitor {

    const std::map<std::string, Type>& sort_map;
    const std::map<std::string, Expr>& const_map;

    std::map<std::string, std::string> const_model;
    std::map<std::string, std::string> const_reprs;

    std::vector<std::shared_ptr<CVC4_ExprDual>> pto_modellers;
    std::vector<std::shared_ptr<CVC4_ExprDual>> neq_modellers;

    void _ensure(bool b, const std::string& msg) {
        if (!b) {
            snlog::l_error() << "SL problem contextual error: " << msg << snlog::l_end;
        }
    }

    void compute_creprs() {
        for (const std::pair<std::string, std::string>& cvar : const_model) {
            if (stdutils::ninmap(const_reprs, cvar.second)) {
                const_reprs.emplace(cvar.second, cvar.first);
            }
        }
    }

    void build_neq_modellers() {
        for (auto it = const_model.begin(); it != const_model.end(); ++it) {
            for (auto jt = it; jt != const_model.end(); ++jt) {
                if (it != jt) {
                    if (it->second == jt->second) {
                        auto eqx = std::shared_ptr<CVC4_ExprDual>
                            (new CVC4_ExprDual(const_map.at(it->first),
                                               const_map.at(jt->first),
                                               CVC4_ExprDualSign::CVC4_DS_EQ));
                        neq_modellers.push_back(eqx);
                    } else {
                        auto neqx = std::shared_ptr<CVC4_ExprDual>
                            (new CVC4_ExprDual(const_map.at(it->first),
                                               const_map.at(jt->first),
                                               CVC4_ExprDualSign::CVC4_DS_NEQ));
                        neq_modellers.push_back(neqx);
                    }
                }
            }
        }
    }

    void handle_model(const lisptp::LispTreeNode& node) {
        for (auto leaf : node.getLeaves()) {
            const std::string& lvalue = leaf->getValue();
            if (lvalue == SL_MDL_PMDL_SORT) {
                handle_model_sort(*leaf);
            }
            if (lvalue == SL_MDL_PMDL_FUN) {
                handle_model_fun(*leaf);
            }
        }
    }

    void handle_model_sort(const lisptp::LispTreeNode& node) {
        _ensure(node.getLeaves().size() == 2, "model sort format error");
        auto sname_node = node.getLeaves().at(0);
        _ensure(!sname_node->isCall(), "model sort format error");
        const std::string sname = sname_node->getValue();
        _ensure(stdutils::inmap(sort_map, sname), "unknown model sort name");
    }

    void handle_model_fun(const lisptp::LispTreeNode& node) {
        _ensure(node.getLeaves().size() == 4, "model fun format error");
        auto cname_node = node.getLeaves().at(0);
        auto cvalue_node = node.getLeaves().at(3);
        _ensure(!cname_node->isCall(), "model fun format error");
        _ensure(!cvalue_node->isCall(), "model fun format error");
        const std::string cname = cname_node->getValue();
        const std::string cvalue = cvalue_node->getValue();
        const_model.emplace(cname, cvalue);
    }

    void handle_heap(const lisptp::LispTreeNode& node) {
        compute_creprs();
        for (auto leaf : node.getLeaves())
            handle_heap_line(*leaf);
    }

    void handle_heap_line(const lisptp::LispTreeNode& node) {
        if (node.getValue() == "pto") {
            _ensure(node.getLeaves().size() == 2, "pto heap line format error");
            auto left_node = node.getLeaves().at(0);
            auto right_node = node.getLeaves().at(1);
            _ensure(!left_node->isCall(), "pto heap line format error");
            _ensure(!right_node->isCall(), "pto heap line format error");
            const std::string left = left_node->getValue();
            const std::string right = right_node->getValue();
            _ensure(stdutils::inmap(const_reprs, left), "unknown ptol reference in model");
            _ensure(stdutils::inmap(const_reprs, right), "unknown ptor reference in model");
            const std::string& lrep = const_reprs.at(left);
            const std::string& rrep = const_reprs.at(right);
            _ensure(stdutils::inmap(const_map, lrep), "internal representant mismatch");
            _ensure(stdutils::inmap(const_map, rrep), "internal representant mismatch");
            auto ptox = std::shared_ptr<CVC4_ExprDual>
                (new CVC4_ExprDual(const_map.at(lrep),
                                   const_map.at(rrep),
                                   CVC4_ExprDualSign::CVC4_DS_UNDEF));
            pto_modellers.push_back(ptox);
        } else {
            snlog::l_message() << "Non pto heap model line @" << node.getValue()
                               << " ---> skipping." << snlog::l_end;
        }
    }

public:

    SLModelVisitor(const std::map<std::string, Type>& sort_map,
                   const std::map<std::string, Expr>& const_map)
        : sort_map(sort_map), const_map(const_map) {}

    inline const std::vector<std::shared_ptr<CVC4_ExprDual>>& get_pto_modellers()
    { return pto_modellers; }
    inline const std::vector<std::shared_ptr<CVC4_ExprDual>>& get_neq_modellers()
    { return neq_modellers; }

    void handle(const lisptp::LispTreeNode& node) {
        if (node.isCall()) {
            const std::string& nvalue = node.getValue();
            if (nvalue == "") {
                // Multiple lisp-tree et top level
                for (auto leaf : node.getLeaves())
                    handle(*leaf);
            }
            if (nvalue == SL_MDL_PART_MODEL)
                handle_model(node);
            if (nvalue == SL_MDL_PART_HEAP)
                handle_heap(node);
        } else {
            _ensure(node.getValue() == "sat", "non-sat smt result detected!");
        }
    }

    void extract_implicant(const lisptp::LispTreeNode& node) {
        handle(node);
        build_neq_modellers();
    }

};

#define BUFFER_SIZE 128

static std::string ugly_internal__get_model(const std::string& ifile) {
    std::ifstream source;
    std::ofstream target;
    source.open(ifile);
    target.open(CVC4_SCRIPT_FILE);
    /* Scripting header */
    target << "(set-logic QF_ALL_SUPPORTED)" << '\n'
           << "(set-option :produce-models true)" << '\n'
           << "(set-option :incremental false)" << '\n';
    /* Scripting context */
    std::stringstream ifcontent;
    std::string ifline;
    while (std::getline(source, ifline, '.'))
        target << ifline << '\n';
    source.close();
    /* Scripting commands */
    target << "(check-sat)" << '\n'
           << "(get-model) " << '\n';
    target.close();
    /* Executing script */
    std::array<char, BUFFER_SIZE> buffer;
    std::stringstream result;
    std::string command = CVC4_EXECUTABLE " " CVC4_SCRIPT_FILE;
    std::shared_ptr<FILE> pipe(popen(command.c_str(), "r"), pclose);
    if (!pipe) {
        snlog::l_error() << "Solver execution failure (popen)" << snlog::l_end;
        return "unknown";
    }
    while (!feof(pipe.get())) {
        if (fgets(buffer.data(), 128, pipe.get()) != nullptr) {
            result << buffer.data();
        }
    }
    // TODO: delete CVC4_SCRIPT_FILE
    return result.str();
}

SLProblemContext::SLProblemContext(const Options& opts)
    : opts(opts), em(opts.em), smt(&em), formula(lcl_formula)
{
    if (opts.mode == SLInputMode::Local) {
        hyp_size = opts.mmt.size();
        model_matchTable = opts.mmt;
        separator_0 = opts.sep0;
        separator_1 = opts.sep1;
    } else {
        /* Load File */

        // Start by loading problem file
        snlog::l_message() << "Loading " << opts.input_file << snlog::l_end;
        std::shared_ptr<lisptp::LispTreeNode> pdata = lisptp::parse_file(opts.input_file);
        SLProblemVisitor pvisitor(em);
        pvisitor.handle(*pdata);

        const std::map<std::string, Type>& typeMap = pvisitor.get_sort_map();
        const std::map<std::string, Expr>& exprMap = pvisitor.get_const_map();

        snlog::l_message() << "Recovering input formula..." << snlog::l_end;
        lcl_formula = pvisitor.get_formula();
        snlog::l_notif() << "Input formula is: " << lcl_formula.toString() << snlog::l_end;

        // Recovering and parsing model
        snlog::l_message() << "Recovering initial model..." << snlog::l_end;
        std::string model = ugly_internal__get_model(opts.input_file);
        snlog::l_notif() << "Model is: " << model << snlog::l_end;

        snlog::l_message() << "Extracting implicant from model..." << snlog::l_end;
        SLModelVisitor mvisitor(typeMap, exprMap);
        pdata = lisptp::parse(model);
        mvisitor.extract_implicant(*pdata);

        // Reading non minimal representation
        separator_0 = mvisitor.get_pto_modellers().size();
        separator_1 = separator_0 + mvisitor.get_neq_modellers().size();

        model_matchTable = std::vector<std::shared_ptr<CVC4_ExprDual>>(mvisitor.get_pto_modellers());
        for (const std::shared_ptr<CVC4_ExprDual>& match : mvisitor.get_neq_modellers()) {
            model_matchTable.push_back(match);
        }
        if (separator_0 == 0) {
            // Handling the case of an empty heap
            snlog::l_message() << "Hacking empty heap mismatch..." << snlog::l_end;
            if (exprMap.size() > 0) {
                auto empx = std::shared_ptr<CVC4_ExprDual>
                    (new CVC4_ExprDual(exprMap.at(0), exprMap.at(0),
                                       CVC4_ExprDualSign::CVC4_DS_UNDEF));
                model_matchTable.push_back(empx);
            } else {
                snlog::l_warn() << "Failed to fix empty heap mismatch due to empty const set" << snlog::l_end;
            }
        }

        hyp_size = model_matchTable.size();
        snlog::l_notif() << "Implicant size: " << hyp_size << snlog::l_end;
    }

    smt.reset();
    smt.setOption("incremental", false); // Cannot be used with SL for now
    smt.setOption("produce-models", true);
    smt.setLogic("QF_ALL_SUPPORTED");
    // smt.push(); // Not compatible with non incremental
}
