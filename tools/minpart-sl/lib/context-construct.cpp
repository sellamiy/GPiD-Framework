#include <iostream>
#include <sstream>
#include <stack>
#include <snlog/snlog.hpp>
#include <stdutils/strings.hpp>
#include <context.hpp>

#define CONTEXT_SL_CONSTRUCT_SRC

using namespace CVC4;
using namespace stdutils;
using namespace minpart;
using namespace minpart::slcvc;

enum class internal__mmseType {
    __MMSE_PTO,
    __MMSE_EQS,
    __MMSE_FEMP
};

enum class internal__mmslType {
    __MMSL_PTO,
    __MMSL_EQ,
    __MMSL_NEQ,
    __MMSL_FEMP,
    __MMSL_UNKNOWN
};

static internal__mmslType toMmslType(const std::string& s) {
    if (s.compare("pto") == 0) {
        return internal__mmslType::__MMSL_PTO;
    }
    if (s.compare("eq") == 0) {
        return internal__mmslType::__MMSL_EQ;
    }
    if (s.compare("neq") == 0) {
        return internal__mmslType::__MMSL_NEQ;
    }
    if (s.compare("emp") == 0) {
        return internal__mmslType::__MMSL_FEMP;
    }
    return internal__mmslType::__MMSL_UNKNOWN;
}

enum class internal__fdeType {
    __FDE_AND,
    __FDE_OR,
    __FDE_NOT,
    __FDE_EQ,
    __FDE_PTO,
    __FDE_EMP,
    __FDE_SEP,
    __FDE_WAND,
    __FDE_TRUE,
    __FDE_FALSE,
    __FDE_UNKNOWN
};

static internal__fdeType toFdeType(const std::string& s) {
    if (s.compare("and") == 0) {
        return internal__fdeType::__FDE_AND;
    }
    if (s.compare("or") == 0) {
        return internal__fdeType::__FDE_OR;
    }
    if (s.compare("not") == 0) {
        return internal__fdeType::__FDE_NOT;
    }
    if (s.compare("eq") == 0) {
        return internal__fdeType::__FDE_EQ;
    }
    if (s.compare("pto") == 0) {
        return internal__fdeType::__FDE_PTO;
    }
    if (s.compare("emp") == 0) {
        return internal__fdeType::__FDE_EMP;
    }
    if (s.compare("sep") == 0) {
        return internal__fdeType::__FDE_SEP;
    }
    if (s.compare("wand") == 0) {
        return internal__fdeType::__FDE_WAND;
    }
    if (s.compare("true") == 0) {
        return internal__fdeType::__FDE_TRUE;
    }
    if (s.compare("false") == 0) {
        return internal__fdeType::__FDE_FALSE;
    }
    return internal__fdeType::__FDE_UNKNOWN;
}

const PartitionGeneratorOptions SLProblemContext::generate_partition_options() const {
    PartitionGeneratorOptions
        result(opts.c_blocksize, opts.c_depth, opts.p_blocksize, opts.p_depth,
               true, opts.random);
    return result;
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
        /*
         * Format expected:
         *
         * declare NAME_TYPE \n [any time necessary]
         * var NAME TYPE \n [any time necessary]
         * formula w/o pars postfix \n
         * mmTable_size \n
         * SUBELEM_TYPE FROM TO \n [mmTable_size times]
         */
        // Start by loading problem file
        std::string line;
        std::vector<std::string> ptt;
        std::ifstream pfile(opts.input_file);
        if (!pfile.is_open()) {
            snlog::l_error() << "Could not load " << opts.input_file << snlog::l_end;
        }

        // Reading problem variables

        Type integerType = em.integerType();

        std::map<std::string, Type> typeMap;
        std::map<std::string, Expr> exprMap;

        getline(pfile, line);
        ptt = split(line, " ");
        while (ptt[0] == "declare") {
            typeMap.emplace(ptt[1], em.mkSetType(integerType));
            getline(pfile, line);
            ptt = split(line, " ");
        }
        while (ptt[0] == "var") {
            exprMap.emplace(ptt[1], em.mkVar(ptt[1], typeMap[ptt[2]]));
            getline(pfile, line);
            ptt = split(line, " ");
        }

        // Reading problem formula
        std::stack<Expr> lstk;
        Expr exp1, exp2;
        for (const std::string& s : ptt) {
            switch (toFdeType(s)) {
            case internal__fdeType::__FDE_AND:
                exp1 = lstk.top(); lstk.pop();
                exp2 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::AND, exp1, exp2));
                break;
            case internal__fdeType::__FDE_OR:
                exp1 = lstk.top(); lstk.pop();
                exp2 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::OR, exp1, exp2));
                break;
            case internal__fdeType::__FDE_NOT:
                exp1 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::NOT, exp1));
                break;
            case internal__fdeType::__FDE_EQ:
                exp1 = lstk.top(); lstk.pop();
                exp2 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::EQUAL, exp1, exp2));
                break;
            case internal__fdeType::__FDE_PTO:
                exp1 = lstk.top(); lstk.pop();
                exp2 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::SEP_PTO, exp1, exp2));
                break;
            case internal__fdeType::__FDE_EMP:
                exp1 = lstk.top(); lstk.pop();
                exp2 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::SEP_EMP, exp1, exp2));
                break;
            case internal__fdeType::__FDE_SEP:
                exp1 = lstk.top(); lstk.pop();
                exp2 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::SEP_STAR, exp1, exp2));
                break;
            case internal__fdeType::__FDE_WAND:
                exp1 = lstk.top(); lstk.pop();
                exp2 = lstk.top(); lstk.pop();
                lstk.push(em.mkExpr(kind::SEP_WAND, exp1, exp2));
                break;
            case internal__fdeType::__FDE_TRUE:
                lstk.push(em.mkConst(true));
                break;
            case internal__fdeType::__FDE_FALSE:
                lstk.push(em.mkConst(false));
                break;
            default:
                // Assume variable
                lstk.push(exprMap[s]);
                break;
            }
        }
        lcl_formula = lstk.top();

        // Reading non minimal representation
        getline(pfile, line);
        std::istringstream(line) >> hyp_size;

        model_matchTable = std::vector<std::shared_ptr<CVC4_ExprDual>>(hyp_size);

        internal__mmseType curr = internal__mmseType::__MMSE_PTO;

        for (uint32_t i = 0; i < hyp_size; i++) {
            getline(pfile, line);
            ptt = split(line, " ");
            switch (toMmslType(ptt[0])) {
            case internal__mmslType::__MMSL_PTO:
                new (&(model_matchTable[i])) CVC4_ExprDual(exprMap[ptt[1]], exprMap[ptt[2]],
                                                           CVC4_ExprDualSign::CVC4_DS_UNDEF);
                break;
            case internal__mmslType::__MMSL_EQ:
                if (curr == internal__mmseType::__MMSE_PTO) {
                    separator_0 = i;
                    curr = internal__mmseType::__MMSE_EQS;
                }
                new (&(model_matchTable[i])) CVC4_ExprDual(exprMap[ptt[1]], exprMap[ptt[2]],
                                                           CVC4_ExprDualSign::CVC4_DS_EQ);
                break;
            case internal__mmslType::__MMSL_NEQ:
                if (curr == internal__mmseType::__MMSE_PTO) {
                    separator_0 = i;
                    curr = internal__mmseType::__MMSE_EQS;
                }
                new (&(model_matchTable[i])) CVC4_ExprDual(exprMap[ptt[1]], exprMap[ptt[2]],
                                                           CVC4_ExprDualSign::CVC4_DS_NEQ);
                break;
            case internal__mmslType::__MMSL_FEMP:
                if (curr != internal__mmseType::__MMSE_FEMP) {
                    separator_1 = i;
                    if (curr == internal__mmseType::__MMSE_PTO) {
                        separator_0 = i;
                    }
                    curr = internal__mmseType::__MMSE_FEMP;
                }
                new (&(model_matchTable[i])) CVC4_ExprDual(exprMap[ptt[1]], exprMap[ptt[2]],
                                                           CVC4_ExprDualSign::CVC4_DS_UNDEF);
                break;
            default:
                snlog::l_error() << "Illegal mm subelement in file: " << ptt[0] << snlog::l_end;
                break;
            }
        }
        if (curr != internal__mmseType::__MMSE_FEMP) {
            separator_1 = hyp_size;
            if (curr == internal__mmseType::__MMSE_PTO) {
                separator_0 = hyp_size;
            }
            curr = internal__mmseType::__MMSE_FEMP;
        }

        // Closing locals
        pfile.close();

    }
    smt.setOption("incremental", false); // Cannot be used with SL for now
    smt.setOption("produce-models", true);
    smt.setLogic("QF_ALL_SUPPORTED");
    // smt.push(); // Not compatible with non incremental
}
