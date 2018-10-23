#ifndef GUNITI_EXECUTORS_WRAPPERS_TEMPLATE
#define GUNITI_EXECUTORS_WRAPPERS_TEMPLATE

#ifdef SINGLE_SOLVER_ONLY

{% for interface in data.interfaces %}
#ifdef SINGLE_SOLVER_{{ interface.name }}
#include "{{ interface.mainheader }}"

template void generate<{{ interface.classname }}, {{ interface.generationclass }}>(OptionStorage& opts);

static inline gunitiExecutionStatus wrap_generate(OptionStorage& opts) {
    try {
        generate<{{ interface.classname }}, {{ interface.generationclass }}>(opts);
        return gunitiExecutionStatus::SUCCESS;
    }

    {% for exception_class in interface.exceptions %}
    catch ({{ exception_class.classname }}& e) {
        snlog::l_fatal() << "Solver exception recovered" << snlog::l_end
                         << snlog::l_error << e.{{ exception_class.message_method }}()
                         << snlog::l_end;
        return gunitiExecutionStatus::FAILURE;
    }
    {% endfor %}
    catch (gpid::InternalError& e) {
        snlog::l_internal() << e.what() << snlog::l_end;
        return gunitiExecutionStatus::FAILURE;
    }
    catch (gpid::GPiDError& e) {
        snlog::l_fatal() << e.what() << snlog::l_end;
        return gunitiExecutionStatus::FAILURE;
    }
    catch (std::exception& e) {
        snlog::l_internal() << "Unexpected throwable recovered" << snlog::l_end
                            << snlog::l_fatal << e.what() << snlog::l_end;
        return gunitiExecutionStatus::FAILURE;
    }
}

#endif
{% endfor %}

#else

{% for interface in data.interfaces %}
#include "{{ interface.mainheader }}"
template void generate<{{ interface.classname }}, {{ interface.generationclass }}>(OptionStorage& opts);
{% endfor %}

static inline gunitiExecutionStatus wrap_generate(OptionStorage& opts) {
    switch (opts.interface) {
    {% for interface in data.interfaces %}
    case interface_id::{{ interface.name }}_INTERFACE:
        try {
            generate<{{ interface.classname }}, {{ interface.generationclass }}>(opts);
            return gunitiExecutionStatus::SUCCESS;
        }

        {% for exception_class in interface.exceptions %}
        catch ({{ exception_class.classname }}& e) {
            snlog::l_fatal() << "Solver {{ interface.classname }} exception recovered" << snlog::l_end
                             << snlog::l_error << e.{{ exception_class.message_method }}()
                             << snlog::l_end;
            return gunitiExecutionStatus::FAILURE;
        }
        {% endfor %}
        catch (gpid::InternalError& e) {
            snlog::l_internal() << e.what() << snlog::l_end;
            return gunitiExecutionStatus::FAILURE;
        }
        catch (gpid::GPiDError& e) {
            snlog::l_fatal() << e.what() << snlog::l_end;
            return gunitiExecutionStatus::FAILURE;
        }
        catch (std::exception& e) {
            snlog::l_internal() << "Unexpected throwable recovered" << snlog::l_end
                                << snlog::l_fatal << e.what() << snlog::l_end;
            return gunitiExecutionStatus::FAILURE;
        }
        {% endfor %}
    default:
        snlog::l_internal() << "Unknown solver interface provided" << snlog::l_end;
        return gunitiExecutionStatus::FAILURE;
    }
}
#endif

#endif
