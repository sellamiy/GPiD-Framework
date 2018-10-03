#ifndef MAGIC_LITERAL_BUILDER_f_SMTLIB2__ERRORS_HPP
#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__ERRORS_HPP

#include <string>
#include <exception>

namespace mlbsmt2 {

    class MLB2Error : public std::exception {
        std::string reason;
    public:
        MLB2Error(std::string reason) : reason(reason) { }
        virtual std::string getErrorInfo() const = 0;
        virtual const char* what() const throw () {
            return (getErrorInfo() + " : " + reason).c_str();
        }
    };

    class InternalError : public MLB2Error {
    public:
        InternalError(std::string reason) : MLB2Error(reason) { }
        virtual std::string getErrorInfo() const {
            return "Internal illegal statement";
        }
    };

    class BuilderStatusError : public MLB2Error {
    public:
        BuilderStatusError(std::string reason) : MLB2Error(reason) { }
        virtual std::string getErrorInfo() const {
            return "Builder accessed in an illegal state";
        }
    };

}

#endif
