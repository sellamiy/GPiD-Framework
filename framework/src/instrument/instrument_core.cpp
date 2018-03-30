#define GPID_FRAMEWORK__INSTRUMENT__CORE_CPP

#include <map>
#include <list>
#include <snlog/snlog.hpp>
#include <dot/dotcommand.hpp>
#include <gpid/instrument/instrument.hpp>
#include <gpid/instrument/selection_graph.hpp>
#include <gpid/instrument/webtrace.hpp>

namespace gpid {
namespace instrument {

    /* Finalization handlers */
    typedef void (*finalizer) (InstrumentOptions&, InstrumentController&);
    std::list<finalizer> finalizers;
    extern void finalize(InstrumentOptions& opts, InstrumentController& ctrler) {
        snlog::l_notif("finalize instruments...");
        for (void (*finalizer)(InstrumentOptions&, InstrumentController&) : finalizers) {
            finalizer(opts, ctrler);
        }
    }

    /* Analyses core handler */
    typedef void (*analyzer) (const std::string);
    std::map<instloc, std::list<analyzer> > analyzers;
    extern void analyze(const idata data, instloc analysis) {
        for (void (*analyzer)(const std::string) : analyzers[analysis]) {
            analyzer(data.get());
        }
    }

    /* Wrapping definitions */

    static SelectionGrapher* selectionGrapher;
    static inline void selectionGrapher_stack_push(const std::string)
    { selectionGrapher->confirmSelection(); }
    static inline void selectionGrapher_stack_pop(const std::string)
    { selectionGrapher->backtrackSelection(); }
    static inline void selectionGrapher_pre_select(const std::string d)
    { selectionGrapher->selection(d); }
    static inline void selectionGrapher_implicate(const std::string)
    { selectionGrapher->implicateDetected(); }
    static inline void selectionGrapher_model_skip(const std::string d)
    { selectionGrapher->skip(d, "model"); }
    static inline void selectionGrapher_reset(const std::string)
    { selectionGrapher->initialize(); }

    static inline void selectionGrapher_finalizer
    (InstrumentOptions& opts, InstrumentController&)
    {
        selectionGrapher->terminate();
        if (opts.autocompile_graphs)
            dot::system::autocompile(opts.selection_graph_file, opts.selection_graph_file + ".svg");
    }

    static WebtraceInstrument* webtraceInstrument;
    static std::string webtraceLocalSelect;
    static std::string webtraceSmtTest;
    static inline void webtraceInstrument_stack_push(const std::string)
    { webtraceInstrument->subcall(webtraceLocalSelect); }
    static inline void webtraceInstrument_stack_pop(const std::string)
    { webtraceInstrument->end_subcall(); }
    static inline void webtraceInstrument_pre_select(const std::string d)
    { webtraceLocalSelect = d; }
    static inline void webtraceInstrument_implicate(const std::string)
    { webtraceInstrument->command("Implicate detected"); }
    static inline void webtraceInstrument_model_skip(const std::string d)
    { webtraceInstrument->assign("Skipped via model", d); }
    static inline void webtraceInstrument_ismt_test(const std::string d)
    { webtraceSmtTest = d; }
    static inline void webtraceInstrument_ismt_result(const std::string d)
    { webtraceInstrument->assign(webtraceSmtTest, d); }
    static inline void webtraceInstrument_reset(const std::string)
    { webtraceInstrument->reset(); }

    static inline void webtraceInstrument_finalizer
    (InstrumentOptions&, InstrumentController&)
    { webtraceInstrument->terminate(); }

    /* Instrumentation initializer */
    extern void initialize(InstrumentOptions& opts, InstrumentController& ctrler) {
        snlog::l_notif("initialize instruments...");
        if (opts.selection_graph) {
            selectionGrapher = new SelectionGrapher(ctrler.getSelectionGraphStream());
            analyzers[stack_push].push_back(&selectionGrapher_stack_push);
            analyzers[stack_pop].push_back(&selectionGrapher_stack_pop);
            analyzers[pre_select].push_back(&selectionGrapher_pre_select);
            analyzers[implicate].push_back(&selectionGrapher_implicate);
            analyzers[model_skip].push_back(&selectionGrapher_model_skip);
            analyzers[reset].push_back(&selectionGrapher_reset);
            finalizers.push_back(&selectionGrapher_finalizer);
        }
        if (opts.webtrace) {
            webtraceInstrument = new WebtraceInstrument(ctrler.getWebtraceStream());
            // TODO: Setup Analyzers and finalizers
            analyzers[stack_push].push_back(&webtraceInstrument_stack_push);
            analyzers[stack_pop].push_back(&webtraceInstrument_stack_pop);
            analyzers[pre_select].push_back(&webtraceInstrument_pre_select);
            analyzers[implicate].push_back(&webtraceInstrument_implicate);
            analyzers[model_skip].push_back(&webtraceInstrument_model_skip);
            analyzers[ismt_test].push_back(&webtraceInstrument_ismt_test);
            analyzers[ismt_result].push_back(&webtraceInstrument_ismt_result);
            analyzers[reset].push_back(&webtraceInstrument_reset);
            finalizers.push_back(&webtraceInstrument_finalizer);
        }
    }

}
}
