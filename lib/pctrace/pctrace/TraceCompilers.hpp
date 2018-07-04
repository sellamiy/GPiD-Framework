/**
 * \file pctrace/TraceCompilers.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef LIB_PCTRACE__TRACE_COMPILERS_HPP
#define LIB_PCTRACE__TRACE_COMPILERS_HPP

#include <pctrace/TraceClass.hpp>

namespace pctrace {

    /** Trace compilation backend for bootstrap html pages. */
    class BootstrapWebCompiler : public TraceCompiler {
    public:
        BootstrapWebCompiler(std::ostream& stream) : TraceCompiler(stream) {}

        virtual void open       (const std::string title);
        virtual void maps       (const std::string key, const std::string val);
        virtual void command    (const std::string c);
        virtual void encapsulate(const std::string key, const std::string val);
        virtual void decapsulate();
        virtual void close      ();
    };

}

#endif
