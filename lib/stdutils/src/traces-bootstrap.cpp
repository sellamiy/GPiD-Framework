#define LIB_STANDARD_UTILS__BOOTSTRAP_WEB_COMPILER_CPP

#include <ostream>
#include <stdutils/traces-bootstrap.hpp>

using namespace stdutils;

static uint64_t INTERN_LPCT_BWC_ID = 0;
static inline uint64_t next_id() {
    return ++INTERN_LPCT_BWC_ID;
}

static inline void bootstrap_header(std::ostream& stream) {
    stream << "<!DOCTYPE html>" << std::endl;
    stream << "<html lang=\"en\">" << std::endl;
    stream << "<head>" << std::endl;
    stream << "<meta charset=\"utf-8\">" << std::endl;
    stream << "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1, shrink-to-fit=no\">" << std::endl;
    stream << "<meta name=\"description\" content=\"\">" << std::endl;
    stream << "<meta name=\"author\" content=\"\">" << std::endl;
    stream << "<title>Auto Algorithm Webtrace</title>" << std::endl;
    stream << "<link rel=\"stylesheet\" href=\"https://maxcdn.bootstrapcdn.com/bootstrap/4.0.0/css/bootstrap.min.css\">" << std::endl;
    stream << "</head>" << std::endl;
    stream << "<body>" << std::endl;
    stream << "<div class=\"container\">" << std::endl;
    
}

static inline void bootstrap_algorithm(std::ostream& stream, const std::string& pagetitle) {
    stream << "<div class=\"card\">" << std::endl;
    stream << "<div class=\"card-header\">" << std::endl;
    stream << "<h1>" << pagetitle << "</h1>" << std::endl;
    stream << "</div>" << std::endl;
    stream << "<div class=\"card-body\">" << std::endl;
}

static inline void bootstrap_mapping(std::ostream& stream, const std::string& k, const std::string& v) {

    stream << "<p>" << std::endl;
    stream << "<kbd>" << k << " &larr;</kbd> " << v << std::endl;
}

static inline void bootstrap_command(std::ostream& stream, const std::string& c) {

    stream << "<p>" << std::endl;
    stream << "<kbd>" << c << "</kbd>" << std::endl;
}

static inline void bootstrap_collapse(std::ostream& stream, const std::string& k, const std::string& v) {
    uint64_t collapse_id = next_id();
    stream << "<p>" << std::endl;
    stream << "<div class=\"card\">" << std::endl;
    stream << "<div class=\"card-header\">" << std::endl;
    stream << "<a class=\"card-link\" data-toggle=\"collapse\" href=\"#collapse" << collapse_id << "\">" << std::endl;
    stream << "<kbd>" << k << "(" << v << ")</kbd>" << std::endl;
    stream << "</a>" << std::endl;
    stream << "</div>" << std::endl;
    stream << "<div id=\"collapse" << collapse_id << "\" class=\"collapse\">" << std::endl;
    stream << "<div class=\"card-body\">" << std::endl;
}

static inline void bootstrap_collapse_end(std::ostream& stream) {
    stream << "</div></div></div>" << std::endl;
}

static inline void bootstrap_footer(std::ostream& stream) {
    stream << "</div></div></div>" << std::endl;
    stream << "<script src=\"https://code.jquery.com/jquery-3.2.1.slim.min.js\"></script>" << std::endl;
    stream << "<script src=\"https://cdnjs.cloudflare.com/ajax/libs/popper.js/1.12.9/umd/popper.min.js\"></script>" << std::endl;
    stream << "<script src=\"https://maxcdn.bootstrapcdn.com/bootstrap/4.0.0/js/bootstrap.min.js\"></script>" << std::endl;
    stream << "</body>" << std::endl;
    stream << "</html>" << std::endl;
}



void BootstrapWebCompiler::open(const std::string& title) const {
    bootstrap_header(stream);
    bootstrap_algorithm(stream, title);
}

void BootstrapWebCompiler::maps(const std::string& key, const std::string& val) const {
    bootstrap_mapping(stream, key, val);
}

void BootstrapWebCompiler::command(const std::string& c) const {
    bootstrap_command(stream, c);
}

void BootstrapWebCompiler::encapsulate(const std::string& key, const std::string& val) const {
    bootstrap_collapse(stream, key, val);
}

void BootstrapWebCompiler::decapsulate() const {
    bootstrap_collapse_end(stream);
}

void BootstrapWebCompiler::close() const {
    bootstrap_footer(stream);
}
