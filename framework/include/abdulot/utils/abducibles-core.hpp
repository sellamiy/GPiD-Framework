/**
 * \file abdulot/utils/abducibles-core.hpp
 * \brief Utilities for parsing abducibles files
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__UTILS__ABDPARSER_HPP
#define ABDULOT__UTILS__ABDPARSER_HPP

#include <set>
#include <lisptp/lisptp.hpp>

namespace abdulot {

    using annotation_list_t = std::vector<std::pair<std::string, std::string>>;

    class AbducibleParserVisitor {
        bool valid = true;
        bool handled = false;

        uint32_t size = 0;
        uint32_t rsize = 0;
        bool auto_size = false;

        std::vector<std::string> abddata;
        std::vector<std::string> refdata;
        typename std::vector<std::string>::iterator abdit;
        typename std::vector<std::string>::iterator refit;
        bool ait_init = false;
        bool rit_init = false;

        std::vector<std::string> decls;
        std::map<std::string, std::set<size_t>> annots;
        annotation_list_t defined_annots;

        class Lextender {
            std::map<size_t, size_t> wires;
            std::vector<std::string> extparts;
        public:
            Lextender(const std::vector<std::string>& params, const std::string& extension);
            const std::string extend(const std::vector<std::string>& params) const;
        };

        class AbducibleLambda {
            const std::string name;
            const size_t pcount;
            const Lextender extender;
        public:
            AbducibleLambda(const std::string& name,
                            const std::vector<std::string>& params,
                            const std::string& extension);
            AbducibleLambda(const AbducibleLambda& o)
                : name(o.name), pcount(o.pcount), extender(o.extender) {}

            inline const std::string& get_name() const { return name; }
            inline constexpr size_t get_pcount() const { return pcount; }

            const std::set<std::string> apply
            (const std::vector<std::set<size_t>>& params,
             const std::vector<std::string>& decls,
             const std::set<std::string>& options) const;
        };

        std::map<std::string, AbducibleLambda> lambdas;

        void _ensure(bool b, const std::string& msg);

        void handle_size(const lisptp::LispTreeNode& node);
        void handle_rsize(const lisptp::LispTreeNode& node);
        void handle_abducible(const lisptp::LispTreeNode& node);
        void handle_reference(const lisptp::LispTreeNode& node);
        void handle_extend(const lisptp::LispTreeNode& node);
        void handle_declare(const lisptp::LispTreeNode& node);
        void handle_lambda(const lisptp::LispTreeNode& node);
        void handle_apply(const lisptp::LispTreeNode& node);
        void handle_copy(const lisptp::LispTreeNode& node);
        void handle_annotate(const lisptp::LispTreeNode& node);
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

        inline const annotation_list_t& getAnnotationList() const { return defined_annots; }

        inline constexpr bool isValid() const { return valid; }
        inline constexpr bool isComplete() const { return handled; }
    };

    /** \brief Parser for abducible files. */
    class AbducibleParser {
        std::shared_ptr<lisptp::LispTreeNode> pdata;
        annotation_list_t adata;
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

        const annotation_list_t& getAnnotations();

        /** Check if the parser is in a consistent state. */
        inline constexpr bool isValid() const { return pvisitor.isValid(); }
    };

}

#endif
