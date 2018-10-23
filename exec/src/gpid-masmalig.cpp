#define GPID_EXEC_GPID_MASMALIG_CPP

#include "utils/masmalig-options.hpp"

using namespace std;
using namespace snlog;
using namespace gpid;

struct LiteralPrinter { void handle(const std::string lit); };

inline void LiteralPrinter::handle(const std::string lit) {
    snlog::l_message() << lit << snlog::l_end;
}

struct LiteralExporter {
    ofstream target;
    LiteralExporter(const std::string filename);
    ~LiteralExporter();
    void handle(const std::string lit);
};

LiteralExporter::LiteralExporter(const std::string filename) {
    target.open(filename);
    target << "(size auto)\n";
}

LiteralExporter::~LiteralExporter() {
    target.close();
}

inline void LiteralExporter::handle(const std::string lit) {
    target << "(abduce " << lit << ")\n";
}

int main(int argc, char** argv) {
    OptionStorage opts;
    OptionStatus status = parseOptions(opts, argc, argv);
    if (status == OptionStatus::FAILURE) {
	return EXIT_FAILURE;
    } else if (status == OptionStatus::ENDED) {
	return EXIT_SUCCESS;
    }

    l_message() << "start magically smart literal generator..." << l_end;

    try {
        if (opts.mode == MasmaligHandlingMode::Print) {
            LiteralPrinter printer;
            MasmaligAlgorithm<LiteralPrinter> generator(printer, opts, opts.mopts);
            generator.execute();
        } else if (opts.mode == MasmaligHandlingMode::Export) {
            LiteralExporter exporter(opts.outfile);
            l_info() << "Writing to " << opts.outfile << l_end;
            MasmaligAlgorithm<LiteralExporter> generator(exporter, opts, opts.mopts);
            generator.execute();
        } else {
            snlog::l_internal() << "Unknown masmalig handling mode" << snlog::l_end;
            return EXIT_FAILURE;
        }
        l_message() << "complete." << l_end;
    } catch (mlbsmt2::MLB2Error& e) {
        snlog::l_fatal() << e.what() << snlog::l_end;
        return EXIT_FAILURE;
    } catch (gpid::GPiDError& e) {
        snlog::l_fatal() << e.what() << snlog::l_end;
        return EXIT_FAILURE;
    }

    return EXIT_SUCCESS;

}
