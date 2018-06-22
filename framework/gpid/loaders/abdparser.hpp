/**
 * \file gpid/loaders/abdparser.hpp
 * \brief Utilities for parsing abducibles files
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__LOADERS__ABDPARSER_HPP
#define GPID_FRAMEWORK__LOADERS__ABDPARSER_HPP

#include <fstream>

namespace gpid {

    /** \brief Parser for abducible files. \ingroup gpidcorelib */
    class AbducibleParser {
        std::string source;
        std::ifstream stream;
        struct dw_pstr {
            int line, col;
            inline dw_pstr(int l, int c) : line(l), col(c) {}
        } pos;

        enum class AbdParserStatus { ABDP_0, ABDP_OPENED, ABDP_INIT, ABDP_CLOSED, ABDP_ERROR };
        AbdParserStatus status;

        uint32_t abd_count;

        void openSource();
        void closeSource();

        enum class AbdParserTokenType { ABDC_COMMAND, ABDC_EXPR, ABDC_EOF, ABDC_UNKNOWN };
        struct AbdParserToken {
            AbdParserTokenType type;
            std::string content;
            inline AbdParserToken(const AbdParserTokenType t, const std::string c)
                : type(t), content(c) {}
            inline AbdParserToken(const AbdParserToken& t)
                : type(t.type), content(t.content) {}
        };
        enum class AbdParserState { COMMAND_IN, COMMAND_OUT };
        AbdParserToken lastToken;
        bool lastTokenUse;
        AbdParserToken nextToken(AbdParserState state);
        void skipComment();
        void updateFilePosition(char c);

        void handleError(std::string msg);

        void readHeader();
        void readOption(std::string oname);
    public:
        AbducibleParser(std::string filename);
        ~AbducibleParser();
        void init();
        void setOption(std::string oname, std::string ovalue);

        uint32_t getAbducibleCount();
        std::string nextAbducible();

        inline bool isOk() { return status != AbdParserStatus::ABDP_ERROR; }
    };

}

#endif
