#define WHYML_P_TOOLS_EXECUTABLE_CPP

#include <vector>
#include <cxxopts.hpp>
#include <snlog/snlog.hpp>
#include <whymlp/whymlp.hpp>

using namespace std;
using namespace snlog;
using namespace whymlp;

enum class WhyMLPTool { None, Annotator, Tokenizer, Extractor };

struct WhyMLPToolsOpts {
    vector<string> inputs;
    WhyMLPTool tool;
};

enum class OParseResult { Complete, ToForward, Failed };

static inline OParseResult parse_opts(WhyMLPToolsOpts& opts, int& argc, char**& argv) {
    try {
        cxxopts::Options parser(argv[0], LIBWHYMLP_NAME);

        parser.add_options()
            ("h,help", "Print this help message")
            ("v,version", "Print framework version")
            ("t,tokenize", "Tokenize the source file")
            ("a,annotate", "Annotate the source file")
            ("e,extract", "Extract elements from the source file")

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
            snlog::l_message() << LIBWHYMLP_NAME << " vers. " << LIBWHYMLP_VERSION << snlog::l_end;
            return OParseResult::Complete;
        }

        if (results.count("tokenize")) {
            opts.tool = WhyMLPTool::Tokenizer;
        }
        if (results.count("annotate")) {
            opts.tool = WhyMLPTool::Annotator;
        }
        if (results.count("extract")) {
            opts.tool = WhyMLPTool::Extractor;
        }

        return OParseResult::ToForward;
    } catch (const cxxopts::OptionException& e) {
	l_error() << e.what() << l_end;
	return OParseResult::Failed;
    }
}

static inline int whdl_annotate(const WhyMLPToolsOpts& opts) {
    shared_ptr<AnnotatorParser> parser;
    for (const string& filename : opts.inputs) {
        l_info() << filename << " (annotations)" << l_end;
        parser = shared_ptr<AnnotatorParser>(new AnnotatorParser(filename));
        parser->write(cout);
    }
    if (parser->hasFailed())
        return EXIT_FAILURE;
    else
        return EXIT_SUCCESS;
}

static inline int whdl_tokenize(const WhyMLPToolsOpts& opts) {
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

static inline int whdl_extract(const WhyMLPToolsOpts& opts) {
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
    }
    if (parser->hasFailed())
        return EXIT_FAILURE;
    else
        return EXIT_SUCCESS;
}

int main(int argc, char** argv) {

    try {
        // Handle Options
        WhyMLPToolsOpts opts;
        OParseResult opr = parse_opts(opts, argc, argv);
        if (opr == OParseResult::Complete) return EXIT_SUCCESS;
        if (opr == OParseResult::Failed) return EXIT_FAILURE;

        switch (opts.tool) {
        case WhyMLPTool::Tokenizer:
            return whdl_tokenize(opts);
        case WhyMLPTool::Annotator:
            return whdl_annotate(opts);
        case WhyMLPTool::Extractor:
            return whdl_extract(opts);
        case WhyMLPTool::None:
            l_message() << "Do nothing" << l_end;
            return EXIT_SUCCESS;
        default:
            l_internal() << "Unhandled WhyMLP tool selected: " << "<?>" << l_end;
        }
    } catch (std::exception& e) {
        l_internal() << "Unexpected throwable recovered" << l_end
                     << l_fatal << e.what() << l_end;
    }

    return EXIT_FAILURE;
}
