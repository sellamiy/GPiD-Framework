#define GPID_EXEC_GPID_MASMALIG_CPP

#include "utils/masmalig-options.hpp"

using namespace std;
using namespace snlog;
using namespace gpid;

struct LiteralPrinter { void handle(const std::string lit); };

inline void LiteralPrinter::handle(const std::string lit) {
    snlog::l_message(lit);
}

int main(int argc, char** argv) {
    OptionStorage opts;
    OptionStatus status = parseOptions(opts, argc, argv);
    if (status == OptionStatus::FAILURE) {
	return EXIT_FAILURE;
    } else if (status == OptionStatus::ENDED) {
	return EXIT_SUCCESS;
    }

    l_message("start magically smart literal generator...");

    try {
        LiteralPrinter printer;
        MasmaligAlgorithm<LiteralPrinter> generator(printer, opts, opts.mopts);
        generator.execute();
        l_message("complete.");
    } catch (gpid::GPiDError& e) {
        snlog::l_fatal(e.what());
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;

}
