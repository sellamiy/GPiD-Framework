/**
 * \file smtlib2tools/fileutils.hpp
 * \brief Utilities for handling smtlib2 files.
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_SMTLIB2_CPP_TOOLS__FILE_UTILS__HEADER
#define LIB_SMTLIB2_CPP_TOOLS__FILE_UTILS__HEADER

#include <stdutils/collections.hpp>
#include <smtlib2tools/functions-core.hpp>

namespace smtlib2 {

    class smtfile_decls {
        std::set<smtident_t> symbols;
    public:
        inline const std::set<smtident_t>& get_set() const {
            return symbols;
        }
        inline void add_symbol(const smtident_t& s) {
            symbols.insert(s);
        }
        inline bool is_declared(const smtident_t& s) const {
            return stdutils::inset(symbols, s);
        }
    };

    extern const smtfile_decls extract_declarations(const std::string& filename);

}

#endif
