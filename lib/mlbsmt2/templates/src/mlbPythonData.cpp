#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__PYTHON_DATA_CPP

#include <mlbsmt2/mlbconfig.hpp>

extern const std::vector<std::string> mlb_Py_LoadableScriptTable =
    {
        {% for scriptd in data.scripts %}
        R"({{ scriptd }})",
        {% endfor %}
    };
