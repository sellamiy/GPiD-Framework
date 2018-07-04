/**
 * \file pctrace/TraceClass.hpp
 * \author Yanis Sellami
 * \date 2018
 */
#ifndef LIB_PCTRACE__TRACE_CLASS_HPP
#define LIB_PCTRACE__TRACE_CLASS_HPP

#include <string>
#include <list>

namespace pctrace {

    /** Abstract base class for trace compilation backends. */
    class TraceCompiler {
    protected:
        std::ostream& stream;
    public:
        TraceCompiler(std::ostream& stream) : stream(stream) {}

        virtual void open       (const std::string title) = 0;
        virtual void maps       (const std::string key,
                                 const std::string val)   = 0;
        virtual void command    (const std::string c)     = 0;
        virtual void encapsulate(const std::string key,
                                 const std::string val)   = 0;
        virtual void decapsulate()                         = 0;
        virtual void close      ()                         = 0;
    };

    /** Abstract base class representing a part of an execution trace. */
    class TraceElement {
    public:
        virtual ~TraceElement() {}
        virtual void compile(TraceCompiler& compiler) = 0;
    };

    /** Begining of a trace. */
    class TraceStart : public TraceElement {
        const std::string name;
    public:
        TraceStart(const std::string name) : name(name)   {}
        TraceStart(const TraceStart& o)     : name(o.name) {}

        virtual void compile(TraceCompiler& compiler) {
            compiler.open(name);
        }
    };

    /** Variable assignment in a trace. */
    class TraceVariable : public TraceElement {
        const std::string name;
        const std::string value;
    public:
        TraceVariable(const std::string name, const std::string value)
            : name(name),   value(value)   {}
        TraceVariable(const TraceVariable& o)
            : name(o.name), value(o.value) {}

        virtual void compile(TraceCompiler& compiler) {
            compiler.maps(name, value);
        }
    };

    /** Instruction in a trace. */
    class TraceInstruction : public TraceElement {
        const std::string inst;
    public:
        TraceInstruction(const std::string inst)   : inst(inst)   {}
        TraceInstruction(const TraceInstruction& o) : inst(o.inst) {}

        virtual void compile(TraceCompiler& compiler) {
            compiler.command(inst);
        }
    };

    /** Function call in a trace. */
    class TraceCallStart : public TraceElement {
        const std::string name;
        const std::string params;
    public:
        TraceCallStart(const std::string name, const std::string params)
            : name(name),   params(params)   {}
        TraceCallStart(const TraceCallStart& o)
            : name(o.name), params(o.params) {}

        virtual void compile(TraceCompiler& compiler) {
            compiler.encapsulate(name, params);
        }
    };

    /** Function return in a trace. */
    class TraceCallEnd : public TraceElement {
    public:
        TraceCallEnd()                    {}
        TraceCallEnd(const TraceCallEnd&) {}

        virtual void compile(TraceCompiler& compiler) {
            compiler.decapsulate();
        }
    };

    /** End of a trace. */
    class TraceEnd : public TraceElement {
    public:
        TraceEnd()                {}
        TraceEnd(const TraceEnd&) {}

        virtual void compile(TraceCompiler& compiler) {
            compiler.close();
        }
    };

    /** Execution trace representation. */
    class Trace {
        std::list<TraceElement*> sequence;
    public:
        Trace() {}

        inline void clear() {
            for (TraceElement* e : sequence) {
                delete e;
            }
            sequence.clear();
        }

        inline void traceStart(const std::string tracename)
        { sequence.push_back(new TraceStart(tracename)); }
        inline void traceStop()
        { sequence.push_back(new TraceEnd()); }
        inline void traceVariableValue(const std::string varname, const std::string varvalue)
        { sequence.push_back(new TraceVariable(varname, varvalue)); }
        inline void traceInstruction(const std::string instext)
        { sequence.push_back(new TraceInstruction(instext)); }
        inline void traceCallStart(const std::string funcname, const std::string funcparams)
        { sequence.push_back(new TraceCallStart(funcname, funcparams)); }
        inline void traceCallEnd()
        { sequence.push_back(new TraceCallEnd()); }

        inline void compile(TraceCompiler& compiler) {
            for (TraceElement* e : sequence) {
                e->compile(compiler);
            }
        }
    };

}

#endif
