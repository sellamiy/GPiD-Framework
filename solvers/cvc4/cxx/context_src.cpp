#ifndef GPID_CVC4_CONTEXT_SRC_SPP
#define GPID_CVC4_CONTEXT_SRC_SPP

void gpid::CVC4Declarations::store(CVC4::SymbolTable* table) {
    stable = table;
}

void gpid::CVC4Declarations::collect(CVC4::Command* cmd) {
    cvc4Utils::CVC4DeclBrowser browser(cmd->toString());
    if (browser.containsDeclarations()) {
        std::vector<std::string> decls;
        browser.buildDeclarationList(decls);
        for (const std::string decl : decls) {
            nameDefs.push_back(decl);
        }
    }
}

#endif
