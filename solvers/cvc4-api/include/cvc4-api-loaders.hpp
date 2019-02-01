#ifndef CVC4_API_LOADERS_FOR_GPID__HPP
#define CVC4_API_LOADERS_FOR_GPID__HPP

#include <abdulot/saihelpers/ploader.hpp>
#include "cvc4-api-context.hpp"

namespace gpid {

    using CVC4ContraintsLoader = abdulot::saihelpers::ProblemConstraintsLoader<CVC4Declarations>;

    class CVC4ProblemLoader {
        CVC4::ExprManager ctx;
        CVC4ContraintsLoader consld;
    public:
        CVC4ProblemLoader();

        void load(const std::string filename, const std::string language);

        void prepareReader();
        bool hasConstraint();
        typename CVC4ContraintsLoader::ConstraintT nextConstraint();

        inline CVC4::ExprManager& getContextManager() { return ctx; }
        inline CVC4Declarations& getDeclarations() { return consld.getDeclarations(); }
    };

};

#endif
