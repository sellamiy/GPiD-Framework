/**
 * \file gpid/core/errors.hpp
 * \brief GPiD-Framework Errors Header.
 * \ingroup gpidcorelib
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__ERRORS_HPP
#define GPID_FRAMEWORK__CORE__ERRORS_HPP

#include <string>
#include <exception>

namespace gpid {

    /** \brief Main exception class for the framework related errors */
    class GPiDError : public std::exception {
        std::string reason;
    public:
        /** \brief Constructor \param reason Cause of the exception */
        GPiDError(std::string reason) : reason(reason) { }
        /** \brief Obtain error type textual information. */
        virtual std::string getErrorInfo() const = 0;
        virtual const char* what() const throw () {
            return (getErrorInfo() + " : " + reason).c_str();
        }
    };

    /** \brief Subexception class for errors independent of the problem */
    class GPiDSystemError : public GPiDError
    { public: GPiDSystemError(std::string reason) : GPiDError(reason) { } };

    /** \brief Exception class for internal errors */
    class InternalError : public GPiDSystemError {
    public:
        InternalError(std::string reason) : GPiDSystemError(reason) { }
        virtual std::string getErrorInfo() const {
            return "Framework suffered an internal error";
        }
    };

    /** \brief Exception class for memory errors */
    class MemoryError : public GPiDSystemError {
    public:
        MemoryError(std::string reason) : GPiDSystemError(reason) { }
        virtual std::string getErrorInfo() const {
            return "Failed at a memory operation";
        }
    };

    /** \brief Subexception class for errors dependent of the problem */
    class GPiDInstanceError : public GPiDError
    { public: GPiDInstanceError(std::string reason) : GPiDError(reason) { } };

    /** \brief Exception class for problems solvers can't decide */
    class UndecidableProblemError : public GPiDInstanceError {
    public:
        UndecidableProblemError(std::string reason) : GPiDInstanceError(reason) { }
        virtual std::string getErrorInfo() const {
            return "The problem is undecidable";
        }
    };

    /** \brief Exception class for problems that cannot be parsed */
    class ParseError : public GPiDInstanceError {
    public:
        ParseError(std::string reason) : GPiDInstanceError(reason) { }
        virtual std::string getErrorInfo() const {
            return "The parsing failed";
        }
    };

    /** \brief Exception class for requiring unavailable tool or tool element */
    class UnknownUtilityError : public GPiDInstanceError {
    public:
        UnknownUtilityError(std::string reason) : GPiDInstanceError(reason) { }
        virtual std::string getErrorInfo() const {
            return "Failed at utility selection";
        }
    };

}

#endif
