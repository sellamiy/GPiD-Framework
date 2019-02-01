#define ABDULOT_FRAMEWORK__INSTRUMENT__WEBTRACE_CPP

#include <abdulot/instrument/webtrace.hpp>

using namespace abdulot;

void instrument::WebtraceInstrument::subcall(const std::string selected) {
    tracelog.traceCallStart("Abdulot", selected);
}
void instrument::WebtraceInstrument::end_subcall() {
    tracelog.traceCallEnd();
}
void instrument::WebtraceInstrument::command(const std::string c) {
    tracelog.traceInstruction(c);
}
void instrument::WebtraceInstrument::assign(const std::string k, const std::string v) {
    tracelog.traceVariableValue(k, v);
}

void instrument::WebtraceInstrument::reset() {
    tracelog.clear();
    tracelog.traceStart("Abdulot");
}
void instrument::WebtraceInstrument::terminate() {
    tracelog.traceStop();
    stdutils::BootstrapWebCompiler compiler(target);
    tracelog.compile(compiler);
}
