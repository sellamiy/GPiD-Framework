#define LIB_SMTLIB2_LITERAL_TOOLS__PRESET__SMTLIB2__CPP

#include <fstream>
#include <sstream>
#include <snlog/snlog.hpp>
#include <smtlib2utils/smtlib2utils.hpp>
#include <smtlit/smtlit-annotations.hpp>
#include <smtlit/smtlit-types.hpp>
#include <smtlit/smtlit-presets.hpp>
#include <smtlit/smtlit-fabricator.hpp>

using namespace std;
using namespace smtlit;
using namespace smtlib2utils;

class SMTlib2Handler : public SMTl2CommandHandler {

    SmtLitFabricator& fabricator;
    SmtFunStorage& funstorage;

    inline bool ignore(const SMTl2Command&) { return true; }
    inline bool storeAsUsage(const SMTl2Command&)
    { /* TODO: Handle (?) */ return true; }
    inline bool storeContextData(const SMTl2Command&)
    { /* TODO: Handle (?) */ return true; }
    inline bool storeSortDeclaration(const SMTl2Command&)
    { /* TODO: Handle (?) */ return true; }
    inline bool storeFunDeclaration(const SMTl2Command& cmd);
    inline bool storeConstDeclaration(const SMTl2Command& cmd);
public:
    SMTlib2Handler(SmtLitFabricator& fabricator, SmtFunStorage& funstorage);
};

inline bool SMTlib2Handler::storeFunDeclaration(const SMTl2Command& cmd) {
    auto data = cmd.getDataPtr();
    SMTlib2TokenResult symbol = nextSymbol(*data);
    SMTlib2TokenList plist = nextParameterList__unof(symbol);
    SMTlib2TokenResult rtype = nextSort(*data, plist.end);
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

inline bool SMTlib2Handler::storeConstDeclaration(const SMTl2Command& cmd) {
    auto data = cmd.getDataPtr();
    SMTlib2TokenResult symbol = nextSymbol(*data);
    SMTlib2TokenResult stype = nextSort(symbol);
    fabricator.insert(smtlit_t(symbol.value(), stype.value()), annot_core_const);
    return true;
}

SMTlib2Handler::SMTlib2Handler(SmtLitFabricator& fabricator, SmtFunStorage& funstorage)
    : fabricator(fabricator), funstorage(funstorage)
{
    handlers["assert"] = bind(&SMTlib2Handler::storeAsUsage, this, placeholders::_1);

    handlers["check-sat"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["check-sat-assuming"] = bind(&SMTlib2Handler::storeAsUsage, this, placeholders::_1);

    handlers["declare-const"] = bind(&SMTlib2Handler::storeConstDeclaration, this, placeholders::_1);
    handlers["declare-datatype"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["declare-datatypes"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["declare-fun"] = bind(&SMTlib2Handler::storeFunDeclaration, this, placeholders::_1);
    handlers["declare-sort"] = bind(&SMTlib2Handler::storeSortDeclaration, this, placeholders::_1);
    handlers["define-fun"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["define-fun-rec"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["define-funs-rec"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["define-sort"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);

    handlers["echo"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["exit"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);

    handlers["get-assertions"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-assignment"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-info"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-model"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-option"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-proof"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-unsat-assumptions"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-unsat-core"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["get-value"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);

    handlers["pop"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["push"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["reset"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);
    handlers["reset-assertions"] = bind(&SMTlib2Handler::ignore, this, placeholders::_1);

    handlers["set-info"] = bind(&SMTlib2Handler::storeContextData, this, placeholders::_1);
    handlers["set-logic"] = bind(&SMTlib2Handler::storeContextData, this, placeholders::_1);
    handlers["set-option"] = bind(&SMTlib2Handler::storeContextData, this, placeholders::_1);
}

template<typename SourceT>
static const GenerationSet loc_generate(const SourceT& source) {
    SMTl2StringMemory smem;
    GenerationSet result;
    SmtFunStorage funs;
    SmtLitFabricator& fabricator = result.get_fabricator();
    SMTlib2Handler hdler(fabricator, funs);
    SMTl2CommandParser parser(source, smem);
    parser.initialize();
    parser.parse(hdler);
    snlog::l_warn() << "Partial smtlib2 litegen only" << snlog::l_end;;
    // TODO : More stuff
    FiltrationRule bool_filter(FilterMode::Conjunctive);
    bool_filter.add_filter(FabricationFilter(FilterPolicy::Type_Include, smt_bool));
    fabricator.filter(bool_filter, true);
    return result;
}

template<> const GenerationSet
smtlit::generate_literals<GenerationSource::File, GenerationPreset::SMTlib2>(const string& filename) {
    // Wrap through the smtlib2utils file interface
    return loc_generate<string>(filename);
}

template<> const GenerationSet
smtlit::generate_literals<GenerationSource::Raw, GenerationPreset::SMTlib2>(const string& data) {
    // Wrap through the smtlib2utils string data (via ptr) interface
    shared_ptr<string> _dptr = shared_ptr<string>(new string(data));
    return loc_generate<shared_ptr<string>>(_dptr);
}
