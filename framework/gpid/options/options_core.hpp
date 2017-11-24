/**
 * \file gpid/options/options_core.hpp
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__OPTIONS__CORE_HPP
#define GPID_FRAMEWORK__OPTIONS__CORE_HPP

#include <gpid/config.hpp>
#include <gpid/options/options_engine.hpp>
#include <gpid/options/options_abducibles.hpp>

#include <gpid/options/options_instrument.hpp>

namespace gpid {

    /** \brief Main option structure of the framework. \ingroup gpidcorelib */
    struct CoreOptions {

        /** Options related to abducible hypotheses. */
        AbduciblesOptions abducibles;
        /** Options related to the implicates generator. */
        EngineOptions engine;

        /** Options related to instrumentation tools. */
        instrument::InstrumentOptions instrument;

    };

};

#endif
