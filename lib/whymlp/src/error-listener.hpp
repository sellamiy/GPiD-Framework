#ifndef LIB_WHYMLP__LOCAL_INCLUDE__ERROR_LISTENER_HPP
#define LIB_WHYMLP__LOCAL_INCLUDE__ERROR_LISTENER_HPP

class ErrorListener : public antlr4::BaseErrorListener {
    const string source;
    bool used;
public:
    ErrorListener(const string& source) : source(source), used(false) {}

    inline constexpr bool hasDetectedErrors() const { return used; }

    virtual void syntaxError(antlr4::Recognizer *, antlr4::Token *tk,
                             size_t line, size_t charPositionInLine,
                             const string &msg, exception_ptr) override {
        used = true;
        snlog::l_error() << "Syntax error: " << source << ":\n"
                         << " l." << line << "@" << charPositionInLine << ":\n"
                         << " " << tk->toString() << "\n"
                         << " " << msg << snlog::l_end;
    }
};

#endif
