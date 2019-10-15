#define MINPART_BINTOOLS_SHARED_CODE_CPP

#include <snlog/snlog.hpp>
#include <minpart/minpart.hpp>

template <class Context, class PartitionGenerator>
void shared_execute_main(const typename Context::Options& opts) {
    snlog::l_notif() << "Building minimization problem..." << snlog::l_end;

    Context local(opts);
    PartitionGenerator generator(local.generate_partition_options());
    minpart::GSetEngine<Context> engine(local);
    stdutils::id_box<size_t> idbox(0);

    snlog::l_notif() << "Minimizing..." << snlog::l_end;
    minpart::gsetid
        result = compute_minimal_part(engine, generator, idbox,
                                      engine.generate_full(),
                                      engine.generate_empty(local));
    snlog::l_notifg() << "Minimized!" << snlog::l_end;

    if (!engine.is_coherent(result)) {
        snlog::l_notif() << "-------------------------------" << snlog::l_end;
        snlog::l_error() << "Incoherent result detected" << snlog::l_end;
    }

    snlog::l_notif()
        << "-------------------------------" << snlog::l_end
        << snlog::l_info << "Final Result:" << snlog::l_end
        << snlog::l_notif << "-------------------------------" << snlog::l_end;

    engine.print(result);

    snlog::l_notif() << "-------------------------------" << snlog::l_end;

    // Print Number of calls made to Oracle
    snlog::l_notifg() << "Final Number of Oracle Calls  |  "
                      << engine.get_check_counter() << snlog::l_end;
    snlog::l_notif() << "-------------------------------" << snlog::l_end;

    // TODO: Add the redundancy statistcs printing (see old proto)

    snlog::l_notif() << "Complete." << snlog::l_end;
}

