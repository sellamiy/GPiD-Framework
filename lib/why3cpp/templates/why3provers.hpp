#ifndef LIB_WHY3CPP__PROVERS_CONFIG_HEADER
#define LIB_WHY3CPP__PROVERS_CONFIG_HEADER

#include <string>
#include <why3cpp/why3config.hpp>

namespace why3cpp {

    enum class Why3ConfiguredProver {
        {% for prover in data.provers %}
        {{ prover.replace('-', '_') }},
        {% endfor %}
        UNDEFINED
    };

    static inline Why3ConfiguredProver prover(const std::string& id) {
        {% for prover in data.provers %}
        if (id == "{{ prover }}")
            return Why3ConfiguredProver::{{ prover.replace('-', '_') }};
        {% endfor %}
        return Why3ConfiguredProver::UNDEFINED;
    }

    static inline const std::string str(Why3ConfiguredProver prover) {
        {% for prover in data.provers %}
        if (prover == Why3ConfiguredProver::{{ prover.replace('-', '_') }})
            return "{{ prover }}";
        {% endfor %}
        return "Undef";
    }

    static inline const std::string driver(const std::string& prover) {
        {% for prover in data.provers %}
        if (prover == "{{ prover }}")
            return "{{ data.drivers[prover] }}";
        {% endfor %}
        return "TODO";
    }
    static inline const std::string driver(Why3ConfiguredProver prover) {
        return driver(str(prover));
    }

}

#endif
