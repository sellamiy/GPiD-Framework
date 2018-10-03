#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__SCRIPT_CPP

#include <snlog/snlog.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbscript.hpp>

using namespace smtlib2utils;
using namespace mlbsmt2;

MlbScriptCHandler::MlbScriptCHandler() {
    // handlers["<?>"] = std::bind(&MlbScriptCHandler::handle<?>, this, std::placeholders::_1);
    handlers["const"] = std::bind(&MlbScriptCHandler::handleConst, this, std::placeholders::_1);
    handlers["fun"] = std::bind(&MlbScriptCHandler::handleFun, this, std::placeholders::_1);
    handlers["magic"] = std::bind(&MlbScriptCHandler::handleMagic, this, std::placeholders::_1);

    handlers["apply-fun"] = std::bind(&MlbScriptCHandler::handleApplyFun, this, std::placeholders::_1);
    handlers["apply-eqs"] = std::bind(&MlbScriptCHandler::handleApplyEqs, this, std::placeholders::_1);
    handlers["apply-comps"] = std::bind(&MlbScriptCHandler::handleApplyComps, this, std::placeholders::_1);
}

bool MlbScriptCHandler::handleConst(const SMTl2Command& cmd) {
    SMTlib2TokenResult symbol = nextSymbol(*cmd.getDataPtr());
    SMTlib2TokenResult stype = nextSort(symbol);
    loadedConsts[symbol.value()] = stype.value();
    return true;
}

bool MlbScriptCHandler::handleFun(const SMTl2Command& cmd) {
    SMTlib2TokenResult symbol = nextSymbol(*cmd.getDataPtr());
    SMTlib2TokenList plist = nextParameterList__unof(symbol);
    SMTlib2TokenResult rtype = nextSort(*cmd.getDataPtr(), plist.end);
    if (plist.size() > 0) {
        loadedFuns[symbol.value()] = function_abst_type(plist.value(), rtype.value());
    } else {
        // no-params declared funs are consts
        loadedConsts[symbol.value()] = rtype.value();
    }
    return true;
}

bool MlbScriptCHandler::handleMagic(const SMTl2Command& cmd) {
    snlog::l_warn("For now, magic keyword handles hardcoded integer magics only");
    SMTlib2TokenResult magic = nextNumeral(*cmd.getDataPtr());
    loadedConsts[magic.value()] = "Int";
    return true;
}

bool MlbScriptCHandler::handleApplyFun(const SMTl2Command& cmd) {
    SMTlib2TokenResult symbol = nextSymbol(*cmd.getDataPtr());
    applications.push_back(MlbApplication(MlbApplicationType::Function, symbol.value()));
    return true;
}

bool MlbScriptCHandler::handleApplyEqs(const SMTl2Command& cmd) {
    SMTlib2TokenList types = nextParameterListNoPar__unof(*cmd.getDataPtr());
    if (types.size() > 0) {
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "=", types.value()));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "distinct", types.value()));
    } else {
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "="));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "distinct"));
    }
    return true;
}

bool MlbScriptCHandler::handleApplyComps(const SMTl2Command& cmd) {
    SMTlib2TokenList types = nextParameterListNoPar__unof(*cmd.getDataPtr());
    if (types.size() > 0) {
        applications.push_back(MlbApplication(MlbApplicationType::Equality, ">", types.value()));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, ">=", types.value()));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "<", types.value()));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "<=", types.value()));
    } else {
        applications.push_back(MlbApplication(MlbApplicationType::Equality, ">"));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, ">="));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "<"));
        applications.push_back(MlbApplication(MlbApplicationType::Equality, "<="));
    }
    return true;
}

void MlbScriptParser::_parse() {
    cparser.initialize();
    cparser.parse(chandler);
}

