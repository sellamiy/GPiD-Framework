#define GPID_FRAMEWORK__INSTRUMENT__WEBTRACE_CPP

#include <gpid/instrument/webtrace.hpp>

using namespace gpid;

void instrument::WebtraceInstrument::subcall(const std::string selected) {
    tracelog.traceCallStart("GPiD", selected);
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
    tracelog.traceStart("GPiD");
}
void instrument::WebtraceInstrument::terminate() {
    tracelog.traceStop();
    pctrace::BootstrapWebCompiler compiler(target);
    tracelog.compile(compiler);
}
