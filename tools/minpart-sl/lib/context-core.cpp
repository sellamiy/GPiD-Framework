#include <iostream>
#include <snlog/snlog.hpp>
#include <context.hpp>

#define CONTEXT_SL_SRC

using namespace CVC4;
using namespace minpart;
using namespace minpart::slcvc;

bool SLProblemContext::is_empty_element(uint32_t element, size_t index) const {
    if (index < separator_0) {
        return element > 2; // level 0 == pto, level 1 == not emp, level 2 == true
    } else if (index < separator_1) {
        return element > 0; // level 0 == eq or diseq
    } else {
        return element > 1; // level 0 == emp, level 1 == true
    }
}

bool SLProblemContext::is_generalizable_element(uint32_t element, size_t index) const {
    if (index < separator_0) {
        return element < 2;
    } else if (index < separator_1) {
        return element == 0; // Hack for possible generalization by removal as (1) for eq/diseq
    } else {
        return element == 0;
    }
}

uint32_t SLProblemContext::removal_level(uint32_t, size_t index) const {
    if (index < separator_0) {
        return 3;
    } else if (index < separator_1) {
        return 2; // Idem, Hack for a superficial level for minimization by removal for eq/diseq
    } else {
        return 2;
    }
}

void SLProblemContext::compute_expression(uint32_t element, size_t index) {
    if (index < separator_0) {
        switch (element) {
        case 0:
            bld_formula =
                em.mkExpr(kind::SEP_PTO,
                          model_matchTable.at(index)->df, model_matchTable.at(index)->dt);
            break;
        case 1:
            bld_formula =
                em.mkExpr(kind::NOT,
                          em.mkExpr(kind::SEP_EMP,
                                    model_matchTable.at(index)->df,
                                    model_matchTable.at(index)->dt));
            break;
        case 2:
            bld_formula = em.mkConst(true);
            break;
        default:
            // Hack. This formula should not be used
            bld_formula = em.mkConst(true);
            break;
        }
    } else if (index < separator_1) {
        if (element == 0) {
            if (model_matchTable.at(index)->sign == CVC4_ExprDualSign::CVC4_DS_EQ) {
                bld_formula =
                    em.mkExpr(kind::EQUAL,
                              model_matchTable.at(index)->df, model_matchTable.at(index)->dt);
            } else if (model_matchTable.at(index)->sign == CVC4_ExprDualSign::CVC4_DS_NEQ) {
                bld_formula =
                    em.mkExpr(kind::DISTINCT,
                              model_matchTable.at(index)->df, model_matchTable.at(index)->dt);
            } else {
                snlog::l_warn() << "Undefined equality type for equality subformula!" << snlog::l_end;
            }
        } else {
            // Hack. This formula should not be used
            bld_formula = em.mkConst(true);
        }
    } else {
        if (element == 0) {
            bld_formula =
                em.mkExpr(kind::SEP_EMP,
                          model_matchTable.at(index)->df, model_matchTable.at(index)->dt);
        } else if (element == 1) {
            bld_formula = em.mkConst(true);
        } else {
            // Hack. This formula should not be used
            bld_formula = em.mkConst(true);
        }
    }
}

bool SLProblemContext::is_coherent_hypothesis(const std::vector<uint32_t>& hyp) {
    clear_engine();
    assert_model_formula(true);
    assert_hypothesis(hyp);
    return engine_query(true);
}

bool SLProblemContext::is_valid_hypothesis(const std::vector<uint32_t>& hyp) {
    clear_engine();
    assert_model_formula();
    assert_hypothesis(hyp);
    return engine_query();
}

void SLProblemContext::print_problem() const {
    snlog::l_notif() << "==========<[ PROBLEM ]>==========" << snlog::l_end;
    snlog::l_notif() << formula << snlog::l_end;
    snlog::l_notif() << "=================================" << snlog::l_end;
}

void SLProblemContext::print(uint32_t element, size_t index) {
    compute_expression(element, index);
    std::cout << bld_formula << " ";
}

// Private members

void SLProblemContext::clear_engine() {
    /*
    // Version for incremental usage
      smt.pop();
      smt.push();
    */
    // smt.resetAssertions(); // TODO: Maybe a full reset is necessary
    /* // Version for non incremental usage */
    smt.reset(); // Trying full reset. In this case we also need to reset options
    smt.setOption("incremental", false); // Cannot be used with SL for now
    smt.setOption("produce-models", true);
    smt.setLogic("QF_ALL_SUPPORTED");
}

bool SLProblemContext::engine_query(bool expected, bool notify_ukn) {
    Result qres = smt.checkSat();
    if (notify_ukn && qres.isSat() == Result::SAT_UNKNOWN) {
        snlog::l_warn() << "CVC4 SMT engine returned UNKNOWN!" << snlog::l_end;
    }
    return (!expected && qres.isSat() == Result::UNSAT)
        || (expected && qres.isSat() == Result::SAT);
}

void SLProblemContext::assert_model_formula(bool positive) {
    if (positive) {
        smt.assertFormula(formula);
    } else {
        smt.assertFormula(em.mkExpr(kind::NOT, formula));
    }
}

void SLProblemContext::compute_assertion(const std::vector<uint32_t>& hyp) {
    /* This computes the assertion from an hypothesis following the
       separated points-to and equalities method. */
    Expr h_cons, s_cons;
    bool h_set = false, s_set = false;
    for (uint32_t i = 0; i < hyp_size ; i++) {
        if (!is_empty_element(hyp.at(i), i)) {
            compute_expression(hyp.at(i), i);
            if (i < separator_0 || i == separator_1) {
                if (h_set) {
                    h_cons = em.mkExpr(kind::SEP_STAR, h_cons, bld_formula);
                } else {
                    h_cons = bld_formula;
                    h_set = !h_set;
                }
            } else if (i < separator_1) { // TODO: I believe the condition is redundant
                if (s_set) {
                    s_cons = em.mkExpr(kind::AND, s_cons, bld_formula);
                } else {
                    s_cons = bld_formula;
                    s_set = !s_set;
                }
            }
        }
    }

    if (h_set && s_set) {
        bld_formula = em.mkExpr(kind::AND, h_cons, s_cons);
    } else if (h_set != s_set) {
        bld_formula = h_set ? h_cons : s_cons;
    } else {
        snlog::l_warn() << "Empty formulae handling not implemented!" << snlog::l_end;
        // TODO. Empty formula
    }
}

void SLProblemContext::assert_hypothesis(const std::vector<uint32_t>& hyp) {
    compute_assertion(hyp);
    smt.assertFormula(bld_formula);
}
