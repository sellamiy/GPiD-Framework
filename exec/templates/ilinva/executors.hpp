#ifndef ILINVA_EXECUTORS_WRAPPERS_TEMPLATE
#define ILINVA_EXECUTORS_WRAPPERS_TEMPLATE

{% for code_handler in data.code_handlers %}

#ifdef ILINVA_CODE_HANDLER_{{ code_handler.name }}
#include "{{ code_handler.mainheader }}"

#ifdef SINGLE_SOLVER_ONLY

{% for interface in code_handler.interfaces %}
#ifdef SINGLE_SOLVER_{{ interface.name }}
#include "{{ interface.mainheader }}"

template void generate<{{ code_handler.classname }}, {{ interface.classname }}>(OptionStorage& opts);

static inline ilinvaExecutionStatus wrap_generate(OptionStorage& opts) {
    try {
        generate<{{ code_handler.classname }}, {{ interface.classname }}>(opts);
        return ilinvaExecutionStatus::SUCCESS;
    }

    {% for exception_class in interface.exceptions %}
    catch ({{ exception_class.classname }}& e) {
        snlog::l_fatal() << "Solver exception recovered" << snlog::l_end
                         << snlog::l_error << e.{{ exception_class.message_method }}()
                         << snlog::l_end;
        return ilinvaExecutionStatus::FAILURE;
    }
    {% endfor %}
    {% for exception_class in code_handler.exceptions %}
    catch ({{ exception_class.classname }}& e) {
        snlog::l_fatal() << "Ich exception recovered" << snlog::l_end
                         << snlog::l_error << e.{{ exception_class.message_method }}()
                         << snlog::l_end;
        return ilinvaExecutionStatus::FAILURE;
    }
    {% endfor %}
    catch (gpid::InternalError& e) {
        snlog::l_internal() << e.what() << snlog::l_end;
        return ilinvaExecutionStatus::FAILURE;
    }
    catch (gpid::GPiDError& e) {
        snlog::l_fatal() << e.what() << snlog::l_end;
        return ilinvaExecutionStatus::FAILURE;
    }
    catch (std::exception& e) {
        snlog::l_internal() << "Unexpected throwable recovered" << snlog::l_end
                            << snlog::l_fatal << e.what() << snlog::l_end;
        return ilinvaExecutionStatus::FAILURE;
    }
}

#endif
{% endfor %}

#else

{% for interface in code_handler.interfaces %}
#include "{{ interface.mainheader }}"
template void generate<{{ code_handler.classname }}, {{ interface.classname }}>(OptionStorage& opts);
{% endfor %}

static inline ilinvaExecutionStatus wrap_generate(OptionStorage& opts) {
    switch (opts.interface) {
    {% for interface in code_handler.interfaces %}
    case interface_id::{{ interface.name }}_INTERFACE:
        try {
            generate<{{ code_handler.classname }}, {{ interface.classname }}>(opts);
            return ilinvaExecutionStatus::SUCCESS;
        }

        {% for exception_class in interface.exceptions %}
        catch ({{ exception_class.classname }}& e) {
            snlog::l_fatal()
                << "Solver {{ interface.classname }} exception recovered" << snlog::l_end
                << snlog::l_error << e.{{ exception_class.message_method }}() << snlog::l_end;
            return ilinvaExecutionStatus::FAILURE;
        }
        {% endfor %}
        {% for exception_class in code_handler.exceptions %}
        catch ({{ exception_class.classname }}& e) {
        snlog::l_fatal() << "Ich {{ code_handler.classname }} exception recovered" << snlog::l_end
                         << snlog::l_error << e.{{ exception_class.message_method }}()
                         << snlog::l_end;
        return ilinvaExecutionStatus::FAILURE;
        }
        {% endfor %}
        catch (gpid::InternalError& e) {
            snlog::l_internal() << e.what() << snlog::l_end;
            return ilinvaExecutionStatus::FAILURE;
        }
        catch (gpid::GPiDError& e) {
            snlog::l_fatal() << e.what() << snlog::l_end;
            return ilinvaExecutionStatus::FAILURE;
        }
        catch (std::exception& e) {
            snlog::l_internal() << "Unexpected throwable recovered" << snlog::l_end
                                << snlog::l_fatal << e.what() << snlog::l_end;
            return ilinvaExecutionStatus::FAILURE;
        }
        {% endfor %}
    default:
        snlog::l_internal() << "Unknown solver interface provided" << snlog::l_end;
        return ilinvaExecutionStatus::FAILURE;
    }
}
#endif

#include "{{ code_handler.converters }}"

#endif

{% endfor %}

#endif
