#define GPID_FRAMEWORK__INSTRUMENT__CORE_CPP

#include <map>
#include <list>
#include <snlog/snlog.hpp>
#include <dot/dotcommand.hpp>
#include <gpid/instrument/instrument.hpp>
#include <gpid/instrument/selection_graph.hpp>

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
    typedef void (*analyzer) (void*);
    std::map<analyze_type, std::list<analyzer> > analyzers;
    extern void analyze(void* data, analyze_type analysis) {
        for (void (*analyzer)(void*) : analyzers[analysis]) {
            analyzer(data);
        }
    }

    /* Wrapping definitions */

    static SelectionGrapher* selectionGrapher;
    static inline void selectionGrapher_stack_push(void*)
    { selectionGrapher->confirmSelection(); }
    static inline void selectionGrapher_stack_pop(void*)
    { selectionGrapher->backtrackSelection(); }
    static inline void selectionGrapher_pre_select(void* d)
    { selectionGrapher->selection(*((uint32_t*)d)); }
    static inline void selectionGrapher_implicate(void*)
    { selectionGrapher->implicateDetected(); }
    static inline void selectionGrapher_model_skip(void* d)
    { selectionGrapher->skip(*((uint32_t*)d), "model"); }
    static inline void selectionGrapher_reset(void*)
    { selectionGrapher->initialize(); }

    static inline void selectionGrapher_finalizer
    (InstrumentOptions& opts, InstrumentController&)
    {
        selectionGrapher->terminate();
        if (opts.autocompile_graphs)
            dot::system::autocompile(opts.selection_graph_file, opts.selection_graph_file + ".svg");
    }

    /* Instrumentation initializer */
    extern void initialize(InstrumentOptions& opts, InstrumentController& ctrler) {
        snlog::l_notif("initialize instruments...");
        if (opts.selection_graph) {
            selectionGrapher = new SelectionGrapher(ctrler.getSelectionGraphStream());
            analyzers[stack_push].push_back(&selectionGrapher_stack_push);
            analyzers[stack_pop] .push_back(&selectionGrapher_stack_pop);
            analyzers[pre_select].push_back(&selectionGrapher_pre_select);
            analyzers[implicate].push_back(&selectionGrapher_implicate);
            analyzers[model_skip].push_back(&selectionGrapher_model_skip);
            analyzers[reset].push_back(&selectionGrapher_reset);
            finalizers.push_back(&selectionGrapher_finalizer);
        }
    }

}
}
