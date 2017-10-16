#ifndef GPID_ABDUCIBLES_OPTIONS_HPP
#define GPID_ABDUCIBLES_OPTIONS_HPP

#include <string>

namespace gpid {

    enum AbdInputType { ABDIT_FILE, ABDIT_GENERATOR };

    struct AbduciblesOptions {

        AbdInputType input_type = AbdInputType::ABDIT_GENERATOR;
        std::string input_file;
        std::string input_generator = "<none>";

    };

};

#endif
