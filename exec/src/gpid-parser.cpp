#define GPID_EXEC_GPID_PARSER_CPP

#include "utils/parser-options.hpp"

using namespace std;
using namespace snlog;
using namespace gpid;

int main(int argc, char** argv) {
    ParserOptions opts;
    OptionStatus status = parseOptions(opts, argc, argv);
    if (status == OptionStatus::FAILURE) {
	return EXIT_FAILURE;
    } else if (status == OptionStatus::ENDED) {
	return EXIT_SUCCESS;
    }

    l_message() << "start abducible parser..." << l_end;

    try {
        AbducibleParser parser(opts.input);
        parser.init();
        t_fatal(!parser.isValid()) << "Parser in broken state; please stop!" << l_end;

        l_notif() << "number of abducibles" << " : " << parser.getAbducibleCount() << l_end;

        for (uint32_t i = 0; i < parser.getAbducibleCount(); i++) {
            l_notifg() << "abducible" << " : " << *parser.nextAbducible() << l_end;
        }

        if (parser.isValid()) {
            l_message() << "complete." << l_end;
            return EXIT_SUCCESS;
        } else {
            l_fatal() << "errors were raised." << l_end;
            return EXIT_FAILURE;
        }
    } catch (gpid::GPiDError& e) {
        snlog::l_fatal() << e.what() << snlog::l_end;
        return EXIT_FAILURE;
    }
}
