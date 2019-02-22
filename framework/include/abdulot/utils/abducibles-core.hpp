/**
 * \file abdulot/utils/abducibles-core.hpp
 * \brief Utilities for parsing abducibles files
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__UTILS__ABDPARSER_HPP
#define ABDULOT__UTILS__ABDPARSER_HPP

#include <list>
#include <lisptp/lisptp.hpp>

namespace abdulot {

    class AbducibleParserVisitor {
        bool valid = true;
        bool handled = false;

        uint32_t size = 0;
        uint32_t rsize = 0;
        bool auto_size = false;

        std::list<std::string> abddata;
        std::list<std::string> refdata;
        typename std::list<std::string>::iterator abdit;
        typename std::list<std::string>::iterator refit;
        bool ait_init = false;
        bool rit_init = false;

        void _ensure(bool b, const std::string& msg);

        void handle_size(const lisptp::LispTreeNode& node);
        void handle_rsize(const lisptp::LispTreeNode& node);
        void handle_abducible(const lisptp::LispTreeNode& node);
        void handle_reference(const lisptp::LispTreeNode& node);
    public:
        /** Handler constructor */
        AbducibleParserVisitor() {}

        void handle(const lisptp::LispTreeNode& node);

        /** \return The number of abducible literals after parsing */
        uint32_t getSize();
        uint32_t getRefCount();
        /** \return The next abducible parsed (after parsing, one time iteration) */
        const std::string& nextAbducible();
        const std::string& nextReference();

        inline constexpr bool isValid() const;
        inline constexpr bool isComplete() const;
    };

    /** \brief Parser for abducible files. */
    class AbducibleParser {
        std::shared_ptr<lisptp::LispTreeNode> pdata;
        AbducibleParserVisitor pvisitor;
    public:
        /** Create an abducible file parser. */
        AbducibleParser(const std::string& filename);

        /** Parse the number of abducibles in the file. */
        uint32_t getAbducibleCount();
        uint32_t getReferenceCount();
        /** Parse the next abducible literal in the file. */
        const std::string& nextAbducible();
        const std::string& nextReference();

        /** Check if the parser is in a consistent state. */
        inline constexpr bool isValid() const;
    };

    inline constexpr bool AbducibleParserVisitor::isValid() const { return valid; }
    inline constexpr bool AbducibleParser::isValid() const { return pvisitor.isValid(); }
    inline constexpr bool AbducibleParserVisitor::isComplete() const { return handled; }

}

#endif
