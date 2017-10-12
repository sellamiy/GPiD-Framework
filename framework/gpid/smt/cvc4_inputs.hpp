#ifndef GPID_CVC4_INPUT_HANDLING_HPP
#define GPID_CVC4_INPUT_HANDLING_HPP

#include <gpid/smt/cvc4_engine.hpp>

namespace gpid {

    extern void parse_Cvc(const std::string& filename, CVC4::ExprManager& em, CVC4Problem& pbl);

};

#endif
