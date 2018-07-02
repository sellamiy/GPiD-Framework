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

    l_message("start abducible parser...");

    AbducibleParser parser(opts.input);
    parser.init();
    t_fatal(!parser.isOk(), "Parser in broken state; please stop!");

    l_notif("number of abducibles", parser.getAbducibleCount());

    for (uint32_t i = 0; i < parser.getAbducibleCount(); i++) {
        l_notif("abducible", parser.nextAbducible());
    }

    if (parser.isOk()) {
        l_message("complete.");
        return EXIT_SUCCESS;
    } else {
        l_fatal("errors were raised.");
        return EXIT_FAILURE;
    }
}
