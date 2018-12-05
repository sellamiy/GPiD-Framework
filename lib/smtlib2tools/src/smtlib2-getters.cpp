#define LIB_SMTLIB2_CPP_TOOLS__GETTERS__CPP

#include <smtlib2tools/smtlib2-defs.hpp>
#include <smtlib2tools/smtlib2-annotations.hpp>

using namespace std;
using namespace smtlib2;

extern const smtannotation_t smtlib2::annotation(const smtident_t& i, const smtannotation_map& am) {
    for (const pair<smtannotation_t, set<smtident_t>>& ap : am)
        for (const smtident_t& checkid : ap.second)
            if (checkid == i)
                return ap.first;
    return annot_default;
}
