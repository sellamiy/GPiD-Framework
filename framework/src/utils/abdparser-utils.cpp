#define GPID_FRAMEWORK__UTIL__ABDPARSER_UTIL_CPP

#include <abdulot/core/memory.hpp>
#include <abdulot/utils/abducibles-utils.hpp>

using namespace snlog;
using namespace abdulot;

extern const std::string abdulot::abducibles_memory_id = "Abducibles";
extern const std::string abdulot::references_memory_id = "References";
extern const std::string abdulot::annotations_memory_id = "Annotations";

extern uint32_t abdulot::getAbducibleCount(std::string filename) {
    AbducibleParser parser(filename);
    if (parser.isValid()) {
        return parser.getAbducibleCount();
    } else {
        throw ParseError("Failed to count abducibles in @file:" + filename);
    }
}

extern uint32_t abdulot::getReferenceCount(std::string filename) {
    AbducibleParser parser(filename);
    if (parser.isValid()) {
        return parser.getReferenceCount();
    } else {
        throw ParseError("Failed to count references in @file:" + filename);
    }
}

extern void abdulot::loadAbducibles(std::string filename, AbducibleHandler& handler) {
    size_t size = getAbducibleCount(filename);
    handler.allocate(abducibles_memory_id, size);
    std::map<int, int> linker;
    AbducibleParser parser(filename);
    for (uint32_t i = 0; i < size; i++) {
        if (!parser.isValid()) {
            throw ParseError("Error loading from @file:" + filename);
        }
        handler.handleAbducible(parser.nextAbducible());
    }
}

extern void abdulot::loadReferences(std::string filename, ReferenceHandler& handler) {
    size_t size = getReferenceCount(filename);
    handler.allocate(references_memory_id, size);
    std::map<int, int> linker;
    AbducibleParser parser(filename);
    for (uint32_t i = 0; i < size; i++) {
        if (!parser.isValid()) {
            throw ParseError("Error loading from @file:" + filename);
        }
        handler.handleReference(parser.nextReference());
    }
}

extern void abdulot::loadAnnotations(std::string filename, AnnotationHandler& handler) {
    AbducibleParser parser(filename);
    if (!parser.isValid()) {
        throw ParseError("Error loading from @file:" + filename);
    }
    for (const auto& pair : parser.getAnnotations()) {
        handler.handleAnnotation(pair.first, pair.second);
    }
}

extern void abdulot::loadAbduceData(std::string filename, GenericHandler& handler) {
    // TODO: Do this in a smart way
    loadAbducibles(filename, handler);
    loadReferences(filename, handler);
    loadAnnotations(filename, handler);
}
