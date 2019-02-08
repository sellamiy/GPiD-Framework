#define SMTLIB2_LIB_TOOLS_EXECUTABLE_CPP

#include <cxxopts.hpp>
#include <snlog/snlog.hpp>
#include <smtlib2tools/smtlib2tools.hpp>

using namespace std;
using namespace snlog;
using namespace smtlib2;

enum class ForcedFileFormat { None, Smtlib2, Mlb };

struct ExecOpts {
    vector<smtident_t> reserved;
    vector<string> gfilenames;
    bool foutput = false;
    ForcedFileFormat forced_format = ForcedFileFormat::None;
};

enum class OParseResult { Complete, ToForward, Failed };

static inline OParseResult parse_opts(ExecOpts& opts, int& argc, char**& argv) {
    try {
        cxxopts::Options parser(argv[0], LIB_SMTLIB2_NAME);

        parser.add_options()
            ("h,help", "Print this help message")
            ("v,version", "Print framework version")

            ("check-reserved", "Check if keywords are reserved int smtlib2",
             cxxopts::value<vector<smtident_t>>(opts.reserved))
            ("g,generate-literals", "Generate abducible literals from preset",
             cxxopts::value<vector<string>>(opts.gfilenames))
            ("f,file-output", "Output long results into files",
             cxxopts::value<bool>(opts.foutput))
            ("force-format", "Force input file format", cxxopts::value<string>())
            ;

        cxxopts::ParseResult results = parser.parse(argc, argv);

        vector<string> hcats = {""};

        if (results.count("help")) {
            snlog::l_message() << parser.help(hcats) << snlog::l_end;
            return OParseResult::Complete;
        }
        if (results.count("version")) {
            snlog::l_message() << LIB_SMTLIB2_NAME << " vers. " << LIBSMTLIB2_CPP_VERSION << snlog::l_end;
            return OParseResult::Complete;
        }

        if (results.count("force-format")) {
            const string fmt = results["force-format"].as<string>();
            if (fmt == "mlb") {
                opts.forced_format = ForcedFileFormat::Smtlib2;
            } else if (fmt == "smt2") {
                opts.forced_format = ForcedFileFormat::Mlb;
            } else {
                l_error() << "Unknown file format: " << fmt << l_end;
                l_info() << "Please use mlb or smt2 " << l_end;
                return OParseResult::Failed;
            }
        }

        return OParseResult::ToForward;
    } catch (const cxxopts::OptionException& e) {
	l_error() << e.what() << l_end;
	return OParseResult::Failed;
    }
}

static inline bool is_mlbfile(const string& filename) {
    return filename.substr(filename.find_last_of(".")) == ".mlb";
}

static inline bool is_smtlib2file(const string& filename) {
    return filename.substr(filename.find_last_of(".")) == ".smt2";    
}

static inline const string to_output_file(const string& filename) {
    return filename + ".abduce";
}

static int handle_fwd(ExecOpts& opts) {
    if (opts.reserved.size() > 0) {
        l_info() << "(Reservation checks)" << l_end;
        for (const smtident_t& ident : opts.reserved) {
            l_message() << ident << " : "
                        << (is_reserved(ident) ? "reserved" : "not reserved")
                        << l_end;
        }
    }
    if (opts.gfilenames.size() > 0) {
        for (const string& filename : opts.gfilenames) {
            l_info() << filename << " (literals)" << l_end;
            if (opts.forced_format == ForcedFileFormat::Mlb || is_mlbfile(filename)) {
                auto gset = generate_literals<GenerationSource::File, GenerationPreset::Mlb>(filename);
                if (opts.foutput) {
                    ofstream of(to_output_file(filename));
                    dump<ExportPreset::Abduce>(gset, of);
                    of.close();
                } else {
                    dump<ExportPreset::Raw>(gset, std::cout);
                }
            } else if (opts.forced_format == ForcedFileFormat::Smtlib2 || is_smtlib2file(filename)) {
                auto gset = generate_literals<GenerationSource::File, GenerationPreset::SMTlib2>(filename);
                if (opts.foutput) {
                    ofstream of(to_output_file(filename));
                    dump<ExportPreset::Abduce>(gset, of);
                    of.close();
                } else {
                    dump<ExportPreset::Raw>(gset, std::cout);
                }
            } else {
                l_error() << "Unknown file type (" << filename << ")" << l_end;
                l_info() << "Please convert to mlb or smt2" << l_end;
            }
        }
    }
    return EXIT_SUCCESS;
}

int main(int argc, char** argv) {

    try {
        // Handle Options
        ExecOpts opts;
        OParseResult opr = parse_opts(opts, argc, argv);
        if (opr == OParseResult::Complete) return EXIT_SUCCESS;
        if (opr == OParseResult::Failed) return EXIT_FAILURE;
        return handle_fwd(opts);
    } catch (std::exception& e) {
        l_internal() << "Unexpected throwable recovered" << l_end
                     << l_fatal << e.what() << l_end;
    }

    return EXIT_FAILURE;
}
