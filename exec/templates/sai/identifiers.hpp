#ifndef GPID_EXECUTABLES__SAI__INDENTIFIERS_HPP
#define GPID_EXECUTABLES__SAI__INDENTIFIERS_HPP

enum class interface_id {
    {% for interface in data.interfaces %}
    {{ interface.name }}_INTERFACE,
    {% endfor %}
    UNCONFIGURED_INTERFACE,
    UNKNOWN_INTERFACE
};

static inline interface_id toInterfaceId(std::string v) {
    {% for interface in data.interfaces %}
    if (v == "{{ interface.name }}") {
        return interface_id::{{ interface.name }}_INTERFACE;
    }
    {% endfor %}
    return interface_id::UNKNOWN_INTERFACE;
}

static const std::string interface_id_list =
    "{% for interface in data.interfaces %} {{ interface.name }}{% endfor %}";

#endif
