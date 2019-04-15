/**
 * \file smtlib2tools/string-memory.hpp
 * \brief String allocator for smtlib data.
 * \author Yanis Sellami
 * \date 2019
 */
#ifndef LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_STRING_MEMORY_HPP
#define LIB_SMTLIB2_CPP_TOOLS__SMTLIB2_STRING_MEMORY_HPP

#include <sstream>
#include <memory>
#include <smtlib2tools/smtlib2-defs.hpp>

namespace smtlib2 {

    class StringMemoryData;

    class StringMemory {
        std::unique_ptr<StringMemoryData> data;
    public:
        StringMemory();
        ~StringMemory();

        std::shared_ptr<smtident_t> alloc(const smtident_t& s);
        std::shared_ptr<smtident_t> alloc(const std::stringstream& s);
    };

}

#endif
