#ifndef Z3_API_LOADERS_FOR_GPID__HPP
#define Z3_API_LOADERS_FOR_GPID__HPP

#include <abdulot/saihelpers/ploader.hpp>
#include "z3-api-context.hpp"

using Z3ContraintsLoader = abdulot::saihelpers::ProblemConstraintsLoader<Z3Declarations>;

class Z3ProblemLoader {
    z3::context ctx;
    Z3ContraintsLoader consld;
public:
    Z3ProblemLoader();

    void load(const std::string filename, const std::string language);

    void prepareReader();
    bool hasConstraint();
    typename Z3ContraintsLoader::ConstraintT nextConstraint();

    inline z3::context& getContextManager() { return ctx; }
    inline Z3Declarations& getDeclarations() { return consld.getDeclarations(); }
};

#endif
