/**
 * \file gpid/utils/abdparser.hpp
 * \brief Utilities for parsing abducibles files
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__UTILS__ABDPARSER_HPP
#define GPID_FRAMEWORK__UTILS__ABDPARSER_HPP

#include <list>
#include <smtlib2tools/parser-command.hpp>

namespace gpid {

    /** \brief SMTlib 2 abducible files command handlers */
    class AbducibleParserCommandHandler : public smtlib2::SMTl2CommandHandler {
        uint32_t size = 0;
        bool auto_size = false;

        std::list<std::shared_ptr<std::string>> abddata;
        typename std::list<std::shared_ptr<std::string>>::iterator abdit;
        bool it_init = false;

        bool handleSize(const smtlib2::SMTl2Command& cmd);
        bool handleAbducible(const smtlib2::SMTl2Command& cmd);
        bool handleNothing(const smtlib2::SMTl2Command&);
    public:
        /** Handler constructor */
        AbducibleParserCommandHandler();

        /** \return The number of abducible literals after parsing */
        uint32_t getSize();
        /** \return The next abducible parsed (after parsing, one time iteration) */
        const std::shared_ptr<std::string>& nextAbducible();
    };

    /** \brief Parser for abducible files. */
    class AbducibleParser {
        smtlib2::StringMemory smem;
        smtlib2::SMTl2CommandParser cparser;
        AbducibleParserCommandHandler chandler;
    public:
        /** Create an abducible file parser. */
        AbducibleParser(std::string filename);

        /** Initialize the parser */
        void init();

        /** Parse the number of abducibles in the file. */
        uint32_t getAbducibleCount();
        /** Parse the next abducible literal in the file. */
        const std::shared_ptr<std::string>& nextAbducible();

        /** Check if the parser is in a consistent state. */
        bool isValid();
    };

}

#endif
