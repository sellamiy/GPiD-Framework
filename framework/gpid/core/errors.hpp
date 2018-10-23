/**
 * \file gpid/core/errors.hpp
 * \brief GPiD-Framework Errors Header.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef GPID_FRAMEWORK__CORE__ERRORS_HPP
#define GPID_FRAMEWORK__CORE__ERRORS_HPP

#include <string>
#include <exception>

namespace gpid {

    /** Main exception class for the framework related errors */
    class GPiDError : public std::exception {
        const std::string reason;
    public:
        /** Constructor \param reason Cause of the exception */
        GPiDError(const std::string& reason) : reason(reason) { }
        /** Obtain error type textual information. */
        virtual const std::string getErrorInfo() const = 0;
        /** Textual information of the cause of the error. */
        virtual const char* what() const throw () {
            return (getErrorInfo() + " : " + reason).c_str();
        }
    };

    /** Subexception class for errors independent of the problem */
    class GPiDSystemError : public GPiDError {
    public:
        /** Constructor \param reason Cause of the exception */
        GPiDSystemError(const std::string& reason) : GPiDError(reason) { }
    };

    /** Exception class for internal errors */
    class InternalError : public GPiDSystemError {
    public:
        /** Constructor \param reason Cause of the exception */
        InternalError(const std::string& reason) : GPiDSystemError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Framework suffered an internal error";
        }
    };

    /** Exception class for memory errors */
    class MemoryError : public GPiDSystemError {
    public:
        /** Constructor \param reason Cause of the exception */
        MemoryError(const std::string& reason) : GPiDSystemError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Failed at a memory operation";
        }
    };

    /** Subexception class for errors dependent of the problem */
    class GPiDInstanceError : public GPiDError {
    public:
        /** Constructor \param reason Cause of the exception */
        GPiDInstanceError(const std::string& reason) : GPiDError(reason) { }
    };

    /** Exception class for problems solvers can't decide */
    class UndecidableProblemError : public GPiDInstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        UndecidableProblemError(const std::string& reason) : GPiDInstanceError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "The problem is undecidable";
        }
    };

    /** Exception class for problems that cannot be parsed */
    class ParseError : public GPiDInstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        ParseError(const std::string& reason) : GPiDInstanceError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "The parsing failed";
        }
    };

    /** Exception class for requiring unavailable tool or tool element */
    class UnknownUtilityError : public GPiDInstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        UnknownUtilityError(const std::string& reason) : GPiDInstanceError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Failed at utility selection";
        }
    };

    /** Exception class on accessed instance data */
    class DataError : public GPiDInstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        DataError(const std::string& reason) : GPiDInstanceError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Failure while using instance data";
        }
    };

    /** Exception class for accessing non-existing or forbidden instance data */
    class IllegalAccessError : public DataError {
    public:
        /** Constructor \param reason Cause of the exception */
        IllegalAccessError(const std::string& reason) : DataError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Illegal access to instance data";
        }
    };

}

#endif
