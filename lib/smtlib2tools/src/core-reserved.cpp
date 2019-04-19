#define LIB_SMTLIB2_UTILS__SMTLIB2_RESERVED_KEYWORDS_CHECK_CPP

#include <unordered_set>
#include <smtlib2tools/core.hpp>

namespace smtlib2 {

    static std::unordered_set<smtident_t> ReservedWordsTable = {
        "Bool", "continued-execution", "error", "false", "immediate-exit",
        "incomplete", "logic", "memout", "sat", "success", "theory", "true",
        "unknown", "unsupported", "unsat", ":all-statistics",
        ":assertion-stack-levels", ":authors", ":category", ":chainable",
        ":definition", ":diagnostic-output-channel", ":error-behavior",
        ":extensions", ":funs", ":funs-description", ":global-declarations",
        ":interactive-mode", ":language", ":left-assoc", ":license", ":name",
        ":named", ":notes", ":pattern", ":print-success", ":produce-assignments",
        ":produce-models", ":produce-proofs", ":produce-unsat-assumptions",
        ":produce-unsat-cores", ":random-seed", ":reason-unknown",
        ":regular-output-channel", ":reproducible-resource-limit",
        ":right-assoc", ":smt-lib-version", ":sorts", ":sorts-description",
        ":source", ":status", ":theories", ":values", ":verbosity", ":version",
        "!", "_", "as", "BINARY", "DECIMAL", "exists", "HEXADECIMAL", "forall",
        "let", "match", "NUMERAL", "par", "STRING", "(", ")", "assert",
        "check-sat", "check-sat-assuming", "declare-const", "declare-datatype",
        "declare-datatypes", "declare-fun", "declare-sort", "define-fun",
        "define-fun-rec", "define-sort", "echo", "exit", "get-assertions",
        "get-assignment", "get-info", "get-model", "get-option", "get-proof",
        "get-unsat-assumptions", "get-unsat-core", "get-value", "pop", "push",
        "reset", "reset-assertions", "set-info", "set-logic", "set-option"
    };

    bool is_reserved(const smtident_t& word) {
        return ReservedWordsTable.find(word) != ReservedWordsTable.end();
    }

}
