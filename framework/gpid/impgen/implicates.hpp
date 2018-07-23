/**
 * \file gpid/impgen/implicates.hpp
 * \brief GPiD-Framework Implicate Generator Implicates handlers.
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef GPID_FRAMEWORK__IMPGEN__IMPLICATES_HPP
#define GPID_FRAMEWORK__IMPGEN__IMPLICATES_HPP

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

    /* Implementation */

    template<typename EngineT>
    void BasicImplicateHandler<EngineT>::operator()(EngineT& engine) {
        if (flags.print) engine.printCurrentImplicate();
        if (flags.store) engine.storeCurrentImplicate();
    }

}

#endif
