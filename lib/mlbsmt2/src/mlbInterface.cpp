#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_CPP

#include <snlog/snlog.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbInterface.hpp>

using namespace smtlib2utils;

namespace mlbsmt2 {

    class MagicParsingHandler : public SMTl2CommandHandler {

        std::list<strptr> usage;
        std::list<strptr> context;
        std::list<strptr> funs;
        std::list<strptr> sorts;
        std::list<strptr> consts;

        inline bool ignore(const SMTl2Command&) { return true; }
        bool storeAsUsage(const SMTl2Command& cmd);
        bool storeContextData(const SMTl2Command& cmd);
        bool storeFunDeclaration(const SMTl2Command& cmd);
        bool storeSortDeclaration(const SMTl2Command& cmd);
        bool storeConstDeclaration(const SMTl2Command& cmd);
    public:
        MagicParsingHandler();

        friend MagicLiteralData;
    };

}

using namespace mlbsmt2;

inline bool MagicParsingHandler::storeAsUsage(const SMTl2Command& cmd) {
    usage.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeContextData(const SMTl2Command& cmd) {
    context.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeFunDeclaration(const SMTl2Command& cmd) {
    funs.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeSortDeclaration(const SMTl2Command& cmd) {
    sorts.push_back(cmd.getDataPtr());
    return true;
}

inline bool MagicParsingHandler::storeConstDeclaration(const SMTl2Command& cmd) {
    consts.push_back(cmd.getDataPtr());
    return true;
}

MagicParsingHandler::MagicParsingHandler() {
    handlers["assert"] = std::bind(&MagicParsingHandler::storeAsUsage, this, std::placeholders::_1);

    handlers["check-sat"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["check-sat-assuming"] =
        std::bind(&MagicParsingHandler::storeAsUsage, this, std::placeholders::_1);

    handlers["declare-const"] =
        std::bind(&MagicParsingHandler::storeConstDeclaration, this, std::placeholders::_1);
    handlers["declare-datatype"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["declare-datatypes"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["declare-fun"] =
        std::bind(&MagicParsingHandler::storeFunDeclaration, this, std::placeholders::_1);
    handlers["declare-sort"] =
        std::bind(&MagicParsingHandler::storeSortDeclaration, this, std::placeholders::_1);
    handlers["define-fun"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["define-fun-rec"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["define-funs-rec"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["define-sort"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);

    handlers["echo"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["exit"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);

    handlers["get-assertions"]
        = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-assignment"]
        = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-info"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-model"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-option"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-proof"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-unsat-assumptions"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-unsat-core"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["get-value"] =
        std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);

    handlers["pop"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["push"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["reset"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);
    handlers["reset-assertions"] = std::bind(&MagicParsingHandler::ignore, this, std::placeholders::_1);

    handlers["set-info"] = std::bind(&MagicParsingHandler::storeContextData, this, std::placeholders::_1);
    handlers["set-logic"] = std::bind(&MagicParsingHandler::storeContextData, this, std::placeholders::_1);
    handlers["set-option"] = std::bind(&MagicParsingHandler::storeContextData, this, std::placeholders::_1);
};

/*>---------------------------------------<*/

MagicLiteralData::MagicLiteralData()
    : handler(new MagicParsingHandler()) {}
MagicLiteralData::~MagicLiteralData() {
    handler.release();
}

void MagicLiteralData::storeConst(const std::string name, const std::string type) {
    consts_type_in[type].insert(name);
    consts_name_in[name] = type;
}

void MagicLiteralData::storeFun(const std::string name, const string_list& params,
                                const std::string rtype) {
    funs_type_in[rtype].insert(name);
    funs_name_in[name] = std::pair<string_list, std::string>(params, rtype);
}

void MagicLiteralData::addFunToConsts(std::map<std::string, std::string>& newConsts,
                                      const std::string& funname,
                                      const std::pair<string_list, std::string>& fun) {
    std::vector<string_set::iterator> paramsit;
    std::vector<string_set::iterator> paramsit_begins;
    std::vector<string_set::iterator> paramsit_ends;
    const std::string& rtype = fun.second;
    for (std::string paramt : fun.first) {
        paramsit.push_back(consts_type_in.at(paramt).begin());
        paramsit_begins.push_back(consts_type_in.at(paramt).begin());
        paramsit_ends.push_back(consts_type_in.at(paramt).end());
    }
    bool complete = paramsit.size() == 0;
    if (complete) {
        // function w/o parameters
        std::stringstream ss;
        ss << "(" << funname << ")";
        newConsts[ss.str()] = rtype;
    }
    while (!complete) {
        std::stringstream ss;
        ss << "(" << funname;
        for (auto pit : paramsit)
            ss << " " << *pit;
        ss << ")";
        newConsts[ss.str()] = rtype;
        size_t udt_it = 0;
        paramsit[udt_it]++;
        while (paramsit[udt_it] == paramsit_ends[udt_it]) {
            paramsit[udt_it] = paramsit_begins[udt_it];
            if (++udt_it == paramsit.size()) {
                complete = true;
                break;
            }
            paramsit[udt_it]++;
        }
    }
}

void MagicLiteralData::extractConsts() {
    for (strptr const_data : handler->consts) {
        SMTlib2TokenResult symbol = nextSymbol(*const_data);
        SMTlib2TokenResult stype = nextSort(symbol);
        storeConst(symbol.value(), stype.value());
    }
}

void MagicLiteralData::extractFuns() {
    for (strptr const_data : handler->funs) {
        SMTlib2TokenResult symbol = nextSymbol(*const_data);
        SMTlib2TokenList plist = nextParameterList__unof(symbol);
        SMTlib2TokenResult rtype = nextSort(*const_data, plist.end);
        if (plist.size() > 0)
            storeFun(symbol.value(), plist.value(), rtype.value());
        else
            // no-params declared funs are consts
            storeConst(symbol.value(), rtype.value());
    }
}

void MagicLiteralData::applyFuns() {
    std::map<std::string, std::string> toAdd;
    for (std::pair<const std::string, std::pair<string_list, std::string>>& fun : funs_name_in)
        addFunToConsts(toAdd, fun.first, fun.second);
    for (std::pair<std::string, std::string> nconst : toAdd) {
        consts_type_in[nconst.second].insert(nconst.first);
        consts_name_in[nconst.first] = nconst.second;
    }
}

/*>---------------------------------------<*/

void MagicLiteralBuilder::loadSMTlib2File(const std::string filename) {
    SMTl2CommandParser parser(filename, data.getMemory());
    parser.initialize();
    parser.parse(data.getHandler());
}

bool MagicLiteralBuilder::exploitData(DataExploitation e) {
    switch (e) {
    case DataExploitation::ExtractConsts:
        data.extractConsts();
        break;
    case DataExploitation::ExtractFuns:
        data.extractFuns();
        break;
    case DataExploitation::ApplyFuns:
        data.applyFuns();
        break;
    default:
        return false;
    }
    return true;
}
