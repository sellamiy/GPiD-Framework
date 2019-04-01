#define ABDULOT_FRAMEWORK__INSTRUMENT__CONTROL_CPP

#include <snlog/snlog.hpp>
#include <lcdot/dotcommand.hpp>
#include <abdulot/instrument/instrument.hpp>
#include <abdulot/instrument/infoline.hpp>
#include <abdulot/instrument/graphs.hpp>
#include <abdulot/instrument/webtrace.hpp>

namespace abdulot {
namespace instrument {

    /* Finalization handlers */
    typedef void (*finalizer) (InstrumentOptions&, InstrumentController&);
    std::vector<finalizer> finalizers;
    extern void finalize(InstrumentOptions& opts, InstrumentController& ctrler) {
        snlog::l_notif() << "finalize instruments..." << snlog::l_end;
        for (void (*finalizer)(InstrumentOptions&, InstrumentController&) : finalizers) {
            finalizer(opts, ctrler);
        }
    }

    /* Analyses core handler */
    typedef void (*analyzer) (const std::string);
    std::map<instloc, std::vector<analyzer> > analyzers;
    extern void analyze_data(const idata data, instloc analysis) {
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
    static inline void selectionGrapher_skip(const std::string d)
    // TODO: Split d string @ ':' to separate literal from reason
    { selectionGrapher->skip(d, ""); }
    static inline void selectionGrapher_reset(const std::string)
    { selectionGrapher->initialize(); }

    static inline void selectionGrapher_finalizer
    (InstrumentOptions& opts, InstrumentController&)
    {
        selectionGrapher->terminate();
        if (opts.autocompile_graphs)
            lcdot::system::autocompile(opts.selection_graph_file, opts.selection_graph_file + ".svg");
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
    static inline void webtraceInstrument_skip(const std::string d)
    // TODO: Split d string @ ':' to separate literal from reason
    { webtraceInstrument->assign("Skipped", d); }
    static inline void webtraceInstrument_ismt_test(const std::string d)
    { webtraceSmtTest = d; }
    static inline void webtraceInstrument_ismt_result(const std::string d)
    { webtraceInstrument->assign(webtraceSmtTest, d); }
    static inline void webtraceInstrument_reset(const std::string)
    { webtraceInstrument->reset(); }

    static inline void webtraceInstrument_finalizer
    (InstrumentOptions&, InstrumentController&)
    { webtraceInstrument->terminate(); }

    static InfolineInstrument* infolineInstrument;
    static std::string infolineLocalSelect;
    static inline void infolineInstrument_stack_push(const std::string)
    { infolineInstrument->update_count("depth", 1); }
    static inline void infolineInstrument_stack_pop(const std::string)
    { infolineInstrument->update_count("depth", -1); }
    static inline void infolineInstrument_pre_select(const std::string d)
    {
        infolineInstrument->update_count("preselected", 1);
        infolineInstrument->new_data("preselection", d);
        infolineLocalSelect = d;
    }
    static inline void infolineInstrument_implicate(const std::string)
    {
        infolineInstrument->update_count("implicates", 1);
    }
    static inline void infolineInstrument_skip(const std::string d)
    {
        infolineInstrument->update_count("skipped", 1);
        infolineInstrument->new_data("skip-reason", d);
    }
    static inline void infolineInstrument_ismt_test(const std::string d)
    {
        infolineInstrument->update_count("ismt-tests", 1);
        infolineInstrument->new_data("ismt-reason", d);
    }
    static inline void infolineInstrument_ismt_result(const std::string d)
    {
        infolineInstrument->new_data("ismt-result", d);
    }
    static inline void infolineInstrument_reset(const std::string)
    { infolineInstrument->initialize(); }

    static inline void infolineInstrument_finalizer
    (InstrumentOptions&, InstrumentController&)
    { infolineInstrument->terminate(); }

    /* Instrumentation initializer */
    extern void initialize(InstrumentOptions& opts, InstrumentController& ctrler) {
        snlog::l_notif() << "initialize instruments..." << snlog::l_end;
        if (opts.selection_graph) {
            selectionGrapher = new SelectionGrapher(ctrler.getSelectionGraphStream());
            analyzers[instloc::stack_push].push_back(&selectionGrapher_stack_push);
            analyzers[instloc::stack_pop].push_back(&selectionGrapher_stack_pop);
            analyzers[instloc::pre_select].push_back(&selectionGrapher_pre_select);
            analyzers[instloc::implicate].push_back(&selectionGrapher_implicate);
            analyzers[instloc::skip].push_back(&selectionGrapher_skip);
            analyzers[instloc::reset].push_back(&selectionGrapher_reset);
            finalizers.push_back(&selectionGrapher_finalizer);
        }
        if (opts.webtrace) {
            webtraceInstrument = new WebtraceInstrument(ctrler.getWebtraceStream());
            // TODO: Setup Analyzers and finalizers
            analyzers[instloc::stack_push].push_back(&webtraceInstrument_stack_push);
            analyzers[instloc::stack_pop].push_back(&webtraceInstrument_stack_pop);
            analyzers[instloc::pre_select].push_back(&webtraceInstrument_pre_select);
            analyzers[instloc::implicate].push_back(&webtraceInstrument_implicate);
            analyzers[instloc::skip].push_back(&webtraceInstrument_skip);
            analyzers[instloc::ismt_test].push_back(&webtraceInstrument_ismt_test);
            analyzers[instloc::ismt_result].push_back(&webtraceInstrument_ismt_result);
            analyzers[instloc::reset].push_back(&webtraceInstrument_reset);
            finalizers.push_back(&webtraceInstrument_finalizer);
        }
        if (opts.infoliner) {
            infolineInstrument = new InfolineInstrument();
            analyzers[instloc::stack_push].push_back(&infolineInstrument_stack_push);
            analyzers[instloc::stack_pop].push_back(&infolineInstrument_stack_pop);
            analyzers[instloc::pre_select].push_back(&infolineInstrument_pre_select);
            analyzers[instloc::implicate].push_back(&infolineInstrument_implicate);
            analyzers[instloc::skip].push_back(&infolineInstrument_skip);
            analyzers[instloc::ismt_test].push_back(&infolineInstrument_ismt_test);
            analyzers[instloc::ismt_result].push_back(&infolineInstrument_ismt_result);
            analyzers[instloc::reset].push_back(&infolineInstrument_reset);
            finalizers.push_back(&infolineInstrument_finalizer);
        }
    }

}
}
