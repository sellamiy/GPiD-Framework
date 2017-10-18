#define Z3_CONTEXT

#include <snlog/snlog.hpp>
#include <gpid/smt/cvc4_context.hpp>

using namespace snlog;

void gpid::CVC4Declarations::collect(CVC4::SymbolTable* table) {
    stable = table;
}
