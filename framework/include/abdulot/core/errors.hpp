/**
 * \file abdulot/core/errors.hpp
 * \brief Abdulot Framework Errors Header.
 * \author Yanis Sellami
 * \date 2017
 */
#ifndef ABDULOT__CORE__ERRORS_HPP
#define ABDULOT__CORE__ERRORS_HPP

#include <string>
#include <exception>

namespace abdulot {

    /** Main exception class for the framework related errors */
    class CoreError : public std::exception {
        const std::string reason;
    public:
        /** Constructor \param reason Cause of the exception */
        CoreError(const std::string& reason) : reason(reason) { }
        /** Obtain error type textual information. */
        virtual const std::string getErrorInfo() const = 0;
        /** Textual information of the cause of the error. */
        virtual const char* what() const throw () {
            return (getErrorInfo() + " : " + reason).c_str();
        }
    };

    /** Subexception class for errors independent of the problem */
    class SystemError : public CoreError {
    public:
        /** Constructor \param reason Cause of the exception */
        SystemError(const std::string& reason) : CoreError(reason) { }
    };

    /** Exception class for internal errors */
    class InternalError : public SystemError {
    public:
        /** Constructor \param reason Cause of the exception */
        InternalError(const std::string& reason) : SystemError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Framework suffered an internal error";
        }
    };

    /** Exception class for memory errors */
    class MemoryError : public SystemError {
    public:
        /** Constructor \param reason Cause of the exception */
        MemoryError(const std::string& reason) : SystemError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Failed at a memory operation";
        }
    };

    /** Subexception class for errors dependent of the problem */
    class InstanceError : public CoreError {
    public:
        /** Constructor \param reason Cause of the exception */
        InstanceError(const std::string& reason) : CoreError(reason) { }
    };

    /** Exception class for problems solvers can't decide */
    class UndecidableProblemError : public InstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        UndecidableProblemError(const std::string& reason) : InstanceError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "The problem is undecidable";
        }
    };

    /** Exception class for problems that cannot be parsed */
    class ParseError : public InstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        ParseError(const std::string& reason) : InstanceError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "The parsing failed";
        }
    };

    /** Exception class for requiring unavailable tool or tool element */
    class UnknownUtilityError : public InstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        UnknownUtilityError(const std::string& reason) : InstanceError(reason) { }
        virtual const std::string getErrorInfo() const {
            return "Failed at utility selection";
        }
    };

    /** Exception class on accessed instance data */
    class DataError : public InstanceError {
    public:
        /** Constructor \param reason Cause of the exception */
        DataError(const std::string& reason) : InstanceError(reason) { }
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
