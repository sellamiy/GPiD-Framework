#include <snlog/snlog.hpp>
#include <context-prop-minisat.hpp>

#define CONTEXT_PROP_SRC

using namespace minpart;
using namespace minpart::prop;

bool PropProblemContext::is_coherent_hypothesis(const std::vector<uint32_t>& hyp) {
    assert_hypothesis(hyp);
    return check_modelling();
}

bool PropProblemContext::is_valid_hypothesis(const std::vector<uint32_t>& hyp) {
    assert_hypothesis(hyp);
    return check_modelling();
}

void PropProblemContext::print_problem() const {
    snlog::l_notif() << "==========<[ PROBLEM ]>==========" << snlog::l_end;
    auto& hidden = snlog::l_notif() << "";
    for (int i = 0; i < model.size(); ++i)
        print(0, i);
    hidden << snlog::l_end;
    snlog::l_notif() << "=================================" << snlog::l_end;
}

static inline bool toBool(Minisat::lbool lb) {
    return lb == Minisat::l_True ? false : true;
    // Valid because models are total
}

void PropProblemContext::print(uint32_t element, size_t index) const {
    if (element == 0) {
        Minisat::Lit p = Minisat::mkLit(index, toBool(model[index]));
        std::cout << (p == Minisat::lit_Undef ? "?" : (p.x % 2 == 0 ? "" : "-")) << p.x/2 + 1;
    } else {
        std::cout << "True";
    }
    std::cout << " ";
}

bool PropProblemContext::cmz_satisfied(const Minisat::Clause& c) const {
    for (int i = 0; i < c.size(); ++i) {
        if ((checker[var(c[i])] ^ sign(c[i])) == Minisat::l_True) {
            return true;
        }
    }
    return false;
}

bool PropProblemContext::check_modelling(bool expected) {
    bool mdl_res = true;
    for (Minisat::Var x = 0; x < model.size(); ++x) {
        if (checker[x] == Minisat::l_Undef) {
            Minisat::Lit p = Minisat::mkLit(x, true);
            Minisat::Lit n = Minisat::mkLit(x, false);
            for (int i = 0; i < solver.watches[p].size(); ++i) {
                if (!cmz_satisfied(solver.ca[solver.watches[p][i].cref])) {
                    return false;
                }
            }
            for (int i = 0; i < solver.watches[n].size(); i++) {
                if (!cmz_satisfied(solver.ca[solver.watches[n][i].cref])) {
                    return false;
                }
            }
        }
    }
    
    return (expected && mdl_res)
        || (!expected && !mdl_res);
}

void PropProblemContext::assert_hypothesis(const std::vector<uint32_t>& hyp) {
    checker.clear();
    for (size_t i = 0; i < hyp.size(); ++i) {
        if (hyp.at(i) == 0) {
            checker.push(model[i]);
        } else {
            checker.push(Minisat::l_Undef);
        }
    }
}
