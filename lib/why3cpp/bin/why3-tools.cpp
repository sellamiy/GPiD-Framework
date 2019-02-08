#define WHYML_P_TOOLS_EXECUTABLE_CPP

#include <cxxopts.hpp>
#include <snlog/snlog.hpp>
#include <why3cpp/why3cpp.hpp>

using namespace std;
using namespace snlog;
using namespace why3cpp;

enum class Why3Tool { None, Annotator, Tokenizer, Extractor, Literalizer };

struct Why3ToolsOpts {
    vector<string> inputs;
    Why3Tool tool;
    unsigned int literal_out_format;
};

enum class OParseResult { Complete, ToForward, Failed };

static inline OParseResult parse_opts(Why3ToolsOpts& opts, int& argc, char**& argv) {
    try {
        cxxopts::Options parser(argv[0], LIBWHY3CPP_NAME);

        parser.add_options()
            ("h,help", "Print this help message")
            ("v,version", "Print framework version")
            ("t,tokenize", "Tokenize the source file")
            ("a,annotate", "Annotate the source file")
            ("e,extract", "Extract elements from the source file")
            ("l,literals", "List smtliterals built from the source file (format: 0:Raw; 1:Abd)",
             cxxopts::value<unsigned int>())
            ("input", "Input files", cxxopts::value<vector<string>>(opts.inputs))
            ;
        parser.parse_positional({"input"});
        parser.positional_help("<input-file.mlw> ...");

        cxxopts::ParseResult results = parser.parse(argc, argv);

        vector<string> hcats = {""};

        if (results.count("help")) {
            snlog::l_message() << parser.help(hcats) << snlog::l_end;
            return OParseResult::Complete;
        }
        if (results.count("version")) {
            snlog::l_message() << LIBWHY3CPP_NAME << " vers. " << LIBWHY3CPP_VERSION << snlog::l_end;
            return OParseResult::Complete;
        }

        if (results.count("tokenize")) {
            opts.tool = Why3Tool::Tokenizer;
        }
        if (results.count("annotate")) {
            opts.tool = Why3Tool::Annotator;
        }
        if (results.count("extract")) {
            opts.tool = Why3Tool::Extractor;
        }
        if (results.count("literals")) {
            opts.tool = Why3Tool::Literalizer;
            opts.literal_out_format = results["literals"].as<unsigned int>();
        }

        return OParseResult::ToForward;
    } catch (const cxxopts::OptionException& e) {
	l_error() << e.what() << l_end;
	return OParseResult::Failed;
    }
}

static inline int whdl_annotate(const Why3ToolsOpts& opts) {
    shared_ptr<AnnotatorParser> parser;
    for (const string& filename : opts.inputs) {
        l_info() << filename << " (annotations)" << l_end;
        parser = shared_ptr<AnnotatorParser>(new AnnotatorParser(filename));
        stringstream ss;
        parser->write(ss);
        cout << lisptp::parse(ss.str())->str();
    }
    if (parser->hasFailed())
        return EXIT_FAILURE;
    else
        return EXIT_SUCCESS;
}

static inline int whdl_tokenize(const Why3ToolsOpts& opts) {
    shared_ptr<Tokenizer> parser;
    for (const string& filename : opts.inputs) {
        l_info() << filename << " (antlr tokens)" << l_end;
        parser = shared_ptr<Tokenizer>(new Tokenizer(filename));
        parser->write(cout);
    }
    if (parser->hasFailed())
        return EXIT_FAILURE;
    else
        return EXIT_SUCCESS;
}

static inline int whdl_extract(const Why3ToolsOpts& opts) {
    shared_ptr<ExtractorParser> parser;

    for (const string& filename : opts.inputs) {

        parser = shared_ptr<ExtractorParser>(new ExtractorParser(filename));

        l_info() << filename << " (variables)" << l_end;
        for (const pair<string, string>& var : parser->getVars()) {
            l_message() << var.first << " (" << var.second << ")"
                        << (parser->getRefs().count(var.first) > 0 ? " (ref)" : "")
                        << l_end;
        }

        l_info() << filename << " (literals)" << l_end;
        for (const pair<string, string>& lit : parser->getLits()) {
            l_message() << lit.first << " (" << lit.second << ")" << l_end;
        }

        l_info() << filename << " (applications)" << l_end;
        for (const pair<string, list<vector<string>>>& appl : parser->getAppls()) {
            l_message() << appl.first << " (to)" << l_end;
            for (const auto& plist : appl.second) {
                auto& mrs = l_message() << "     ->";
                for (const string& param : plist) {
                    mrs << " " << param;
                }
                mrs << l_end;
            }
        }
    }

    if (parser->hasFailed())
        return EXIT_FAILURE;
    else
        return EXIT_SUCCESS;
}

static inline int whdl_literalize(const Why3ToolsOpts& opts) {
    shared_ptr<AnnotatorParser> parser;
    shared_ptr<ExtractorParser> vparse;
    for (const string& filename : opts.inputs) {
        l_info() << filename << " (smtlib2 literals)" << l_end;
        auto lset = generate_literals_whyml(filename);
        if (opts.literal_out_format == 0) {
            for (const smtlib2::smtlit_t& lit : lset.get_literals()) {
                l_message() << smtlib2::ident(lit) << " (" << smtlib2::type(lit) << ")" << l_end;
            }
        } else if (opts.literal_out_format == 1) {
            l_message() << "**** file start ****" << l_end;
            // Define size
            std::cout << "(size auto)" << '\n';
            // List references
            vparse = shared_ptr<ExtractorParser>(new ExtractorParser(filename));
            for (const pair<string, string>& var : vparse->getVars()) {
                if (vparse->getRefs().count(var.first) > 0) {
                    std::cout << "(reference " << var.second << ")\n";
                }
            }
            // List abducibles
            for (const smtlib2::smtlit_t& lit : lset.get_literals()) {
                std::cout << "(abduce " << smtlib2::ident(lit) << ")\n";
            }
            l_message() << "***** file end *****" << l_end;
        } else {
            l_error() << "Unknown literalizer output format: "
                      << opts.literal_out_format << l_end
                      << l_info << "Available formats: 0, 1" << l_end
                      << l_message << "0 - Raw format" << l_end
                      << l_message << "1 - Abduce format" << l_end;
        }
    }
    return EXIT_SUCCESS;
}

int main(int argc, char** argv) {

    try {
        // Handle Options
        Why3ToolsOpts opts;
        OParseResult opr = parse_opts(opts, argc, argv);
        if (opr == OParseResult::Complete) return EXIT_SUCCESS;
        if (opr == OParseResult::Failed) return EXIT_FAILURE;

        switch (opts.tool) {
        case Why3Tool::Tokenizer:
            return whdl_tokenize(opts);
        case Why3Tool::Annotator:
            return whdl_annotate(opts);
        case Why3Tool::Extractor:
            return whdl_extract(opts);
        case Why3Tool::Literalizer:
            return whdl_literalize(opts);
        case Why3Tool::None:
            l_message() << "Do nothing" << l_end;
            return EXIT_SUCCESS;
        default:
            l_internal() << "Unhandled Why3 tool selected: " << "<?>" << l_end;
        }
    } catch (std::exception& e) {
        l_internal() << "Unexpected throwable recovered" << l_end
                     << l_fatal << e.what() << l_end;
    }

    return EXIT_FAILURE;
}
