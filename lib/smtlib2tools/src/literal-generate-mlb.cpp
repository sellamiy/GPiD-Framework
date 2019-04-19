#define LIB_SMTLIB2_CPP_TOOLS__PRESET__MLB__CPP

#include <snlog/snlog.hpp>
#include <smtlib2tools/parser-command.hpp>
#include <smtlib2tools/parser-tokens.hpp>
#include <smtlib2tools/literal-presets.hpp>

using namespace std;
using namespace smtlib2;

class MlbHandler : public SMTl2CommandHandler {

    SmtLitFabricator& fabricator;
    SmtFunStorage& funstorage;

    inline const std::vector<smtfun_t> get_funs(const smtident_t& ident);

    inline bool handleConst(const std::string&, const std::string& data);
    inline bool handleFun(const std::string&, const std::string& data);
    inline bool handleMagic(const std::string&, const std::string& data);
    inline bool handleApply(const std::string&, const std::string& data, bool conly);

public:
    MlbHandler(SmtLitFabricator& fabricator, SmtFunStorage& funstorage);
};

inline bool MlbHandler::handleConst(const std::string&, const std::string& data) {
    SMTlib2TokenResult symbol = nextSymbol(data);
    SMTlib2TokenResult stype = nextSort(symbol);
    fabricator.insert(smtlit_t(symbol.value(), stype.value()), annot_core_const);
    return true;
}

static const smttype_t deduce_type(const smtident_t&) {
    snlog::l_warn() << "Int Type via Mlb deduction only @" << __FILE__ << ":" << __LINE__ << snlog::l_end;
    return smt_int;
}

inline bool MlbHandler::handleMagic(const std::string&, const std::string& data) {
    SMTlib2TokenResult magic = nextNumeral(data);
    const smttype_t stype = deduce_type(magic.value());
    fabricator.insert(smtlit_t(magic.value(), stype), annot_core_magic);
    return true;
}

inline bool MlbHandler::handleFun(const std::string&, const std::string& data) {
    SMTlib2TokenResult symbol = nextSymbol(data);
    SMTlib2TokenList plist = nextParameterList__unof(symbol);
    SMTlib2TokenResult rtype = nextSort(data, plist.end);
    if (plist.size() > 0) {
        auto plist_list = plist.value();
        funstorage.insert(smtfun_t(symbol.value(), rtype.value(),
                                   { std::begin(plist_list), std::end(plist_list) }));
    } else {
        // no-params declared funs are const-handable
        fabricator.insert(smtlit_t(symbol.value(), rtype.value()), annot_core_const);
    }
    return true;
}

inline const std::vector<smtfun_t> MlbHandler::get_funs(const smtident_t& ident) {
    std::vector<smtfun_t> res;
    if (funstorage.get_funs().count(ident) > 0) {
        res.push_back(funstorage.get_funs().at(ident));
    } else {
        // Try default functions
        snlog::l_warn() << "Not implemented mlb default functions" << snlog::l_end;;
    }
    return res;
}

inline bool MlbHandler::handleApply(const std::string&, const std::string& data, bool conly) {
    SMTlib2TokenResult symbol = nextSymbol(data);
    for (const smtfun_t& fun : get_funs(symbol.value())) {
        FabricationRule applier(FilterMode::Disjunctive,
                                FabricationPolicy::Apply_Simple,
                                fun, annot_applied);
        if (conly) {
            applier.add_filter(FabricationFilter(FilterPolicy::Annotation_Include, annot_core_const));
            applier.add_filter(FabricationFilter(FilterPolicy::Annotation_Include, annot_core_magic));
        }
        fabricator.fabricate(applier);
    }
    return true;
}

MlbHandler::MlbHandler(SmtLitFabricator& fabricator, SmtFunStorage& funstorage)
    : fabricator(fabricator), funstorage(funstorage)
{
    handlers["const"] = bind(&MlbHandler::handleConst, this, placeholders::_1, placeholders::_2);
    handlers["fun"]   = bind(&MlbHandler::handleFun,   this, placeholders::_1, placeholders::_2);
    handlers["magic"] = bind(&MlbHandler::handleMagic, this, placeholders::_1, placeholders::_2);
    handlers["apply"] = bind(&MlbHandler::handleApply, this, placeholders::_1, placeholders::_2, false);
    handlers["apply-core"] = bind(&MlbHandler::handleApply, this, placeholders::_1, placeholders::_2, true);
}

template<typename SourceT>
static const GenerationSet loc_generate(const SourceT& source) {
    GenerationSet result;
    SmtFunStorage funs;
    SmtLitFabricator& fabricator = result.get_fabricator();
    MlbHandler hdler(fabricator, funs);
    SMTl2CommandParser parser(source);
    parser.parse(hdler);
    FiltrationRule bool_filter(FilterMode::Conjunctive);
    bool_filter.add_filter(FabricationFilter(FilterPolicy::Type_Include, smt_bool));
    fabricator.filter(bool_filter, true);
    return result;
}

template<> const GenerationSet
smtlib2::generate_literals<GenerationSource::File, GenerationPreset::Mlb>(const string& filename) {
    // Wrap through the smtlib2utils file interface
    return loc_generate<string>(filename);
}

template<> const GenerationSet
smtlib2::generate_literals<GenerationSource::Raw, GenerationPreset::Mlb>(const string& data) {
    // Wrap through the smtlib2utils string data (via ptr) interface
    shared_ptr<string> _dptr = shared_ptr<string>(new string(data));
    return loc_generate<shared_ptr<string>>(_dptr);
}
