#ifndef IMPGEN_EXECUTORS_WRAPPERS_TEMPLATE
#define IMPGEN_EXECUTORS_WRAPPERS_TEMPLATE

#ifdef SINGLE_SOLVER_ONLY

{% for interface in data.interfaces %}
#ifdef SINGLE_SOLVER_{{ interface.name }}
#include "{{ interface.name }}/{{ interface.mainheader }}"

template void generate<{{ interface.classname }}>(OptionStorage& opts);

static inline impgenExecutionStatus wrap_generate(OptionStorage& opts) {
    try {
        generate<{{ interface.classname }}>(opts);
        return impgenExecutionStatus::SUCCESS;
    }

    {% for exception_class in interface.exceptions %}
    catch ({{ exception_class.classname }}& e) {
        snlog::l_fatal("Solver exception recovered");
        snlog::l_error(e.{{ exception_class.message_method }}());
        return impgenExecutionStatus::FAILURE;
    }
    {% endfor %}
    catch (gpid::InternalError& e) {
        snlog::l_internal(e.what());
        return impgenExecutionStatus::FAILURE;
    }
    catch (gpid::GPiDError& e) {
        snlog::l_fatal(e.what());
        return impgenExecutionStatus::FAILURE;
    }
    catch (std::exception& e) {
        snlog::l_internal("Unexpected throwable recovered");
        snlog::l_fatal(e.what());
        return impgenExecutionStatus::FAILURE;
    }
}

#endif
{% endfor %}

#else

{% for interface in data.interfaces %}
#include "{{ interface.name }}/{{ interface.mainheader }}"
template void generate<{{ interface.classname }}>(OptionStorage& opts);
{% endfor %}

static inline impgenExecutionStatus wrap_generate(OptionStorage& opts) {
    switch (opts.interface) {
    {% for interface in data.interfaces %}
    case interface_id::{{ interface.name }}_INTERFACE:
        try {
            generate<{{ interface.classname }}>(opts);
            return impgenExecutionStatus::SUCCESS;
        }

        {% for exception_class in interface.exceptions %}
        catch ({{ exception_class.classname }}& e) {
            snlog::l_fatal("Solver {{ interface.classname }} exception recovered");
            snlog::l_error(e.{{ exception_class.message_method }}());
            return impgenExecutionStatus::FAILURE;
        }
        {% endfor %}
        catch (gpid::InternalError& e) {
            snlog::l_internal(e.what());
            return impgenExecutionStatus::FAILURE;
        }
        catch (gpid::GPiDError& e) {
            snlog::l_fatal(e.what());
            return impgenExecutionStatus::FAILURE;
        }
        catch (std::exception& e) {
            snlog::l_internal("Unexpected throwable recovered");
            snlog::l_fatal(e.what());
            return impgenExecutionStatus::FAILURE;
        }
        {% endfor %}
    default:
        snlog::l_internal("Unknown solver interface provided");
        return impgenExecutionStatus::FAILURE;
    }
}
#endif

#endif
