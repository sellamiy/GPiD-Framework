#ifndef MINPART_CONTEXTS_WRAPPERS_TEMPLATE
#define MINPART_CONTEXTS_WRAPPERS_TEMPLATE

#include <minpart-exec/shared-exec.hpp>

{% for mpcontext in data.mpcontexts %}

#ifdef MINPART_CONTEXT_{{ mpcontext.name }}
#include <{{ mpcontext.mainheader }}>

using ExecOpts = {{ mpcontext.optclassname }};

static int handle_fwd(ExecOpts& opts) {
    if (!opts.deterministic) {
        srand (time(NULL));
    }

    snlog::l_notif() << "------------------------------" << snlog::l_end;
    snlog::l_notif() << "Loading Solver..." << snlog::l_end;
    snlog::l_notif() << "------------------------------" << snlog::l_end;
    snlog::l_notif() << "------------------------------" << snlog::l_end;

    shared_execute_main<{{ mpcontext.classname }}, minpart::GenericPartitionGenerator>(opts.local);

    return EXIT_SUCCESS;
}

#endif

{% endfor %}

#endif
