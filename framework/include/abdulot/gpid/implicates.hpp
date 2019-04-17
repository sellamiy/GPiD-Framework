/**
 * \file abdulot/gpid/implicates.hpp
 * \brief Abdulot Framework Implicate Generator Implicates handlers.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef ABDULOT__GPID__IMPLICATES_HPP
#define ABDULOT__GPID__IMPLICATES_HPP

namespace abdulot {
namespace gpid {

    /** Implicate handler for basic operations */
    template<typename EngineT>
    class BasicImplicateHandler {
        struct {
            bool print;
            bool store;
        } flags;
    public:
        /** Initializer */
        BasicImplicateHandler(bool doprint, bool dostore)
            : flags({ .print=doprint, .store=dostore }) {}
        /** Implicate handling operation */
        void operator()(EngineT& engine);
    };

    template<typename LiteralBrowserT, typename LiteralT>
    class AutoforwardExternalChecker {
    public:
        bool operator()(const LiteralBrowserT&, const ObjectMapper<LiteralT>&) const
        { return true; }
    };

    /* Implementation */

    template<typename EngineT>
    void BasicImplicateHandler<EngineT>::operator()(EngineT& engine) {
        if (flags.print) engine.printCurrentImplicate();
        if (flags.store) engine.storeCurrentImplicate();
    }

}
}

#endif
