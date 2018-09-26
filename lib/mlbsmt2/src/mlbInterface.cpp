#define MAGIC_LITERAL_BUILDER_f_SMTLIB2__INTERFACE_CPP

#include <Python.h>
#include <snlog/snlog.hpp>
#include <mlbsmt2/mlbconfig.hpp>
#include <mlbsmt2/mlbInterface.hpp>

class MLBPythonGlobals {
    uint32_t initialized = 0;

    PyObject* pysmtModule;
    PyObject* localModule;

    PyObject* loadFileFunction;

    void load_pysmt_module();
    void load_local_module();
    void unload_modules();

    void load_functions();
    void release_functions();

    PyObject* extract_local_function(const std::string name);
    void release_local_function(PyObject* f);
public:
    void initialize();
    void finalize();

    inline PyObject* get_loadfile_function() { return loadFileFunction; }
};

inline void MLBPythonGlobals::initialize() {
    if (initialized++ == 0) {
        Py_Initialize();
        load_pysmt_module();
        load_local_module();
        load_functions();
    }
}

inline void MLBPythonGlobals::finalize() {
    if (--initialized == 0) {
        release_functions();
        unload_modules();
        if (Py_FinalizeEx() < 0) { /* TODO: notify Error */ }
    }
}

inline void MLBPythonGlobals::load_pysmt_module() {
    PyObject* mname = PyUnicode_DecodeFSDefault("pysmt");
    pysmtModule = PyImport_Import(mname);
    Py_DECREF(mname);
    if (pysmtModule == nullptr) { /* TODO: notify Error */ }
}

inline void MLBPythonGlobals::load_local_module() {
    PyObject* mname = PyUnicode_DecodeFSDefault(MLBSMT2_LOCAL_MODULE);
    localModule = PyImport_Import(mname);
    Py_DECREF(mname);
    if (localModule == nullptr) { /* TODO: notify Error */ }
}

inline void MLBPythonGlobals::unload_modules() {
    Py_DECREF(localModule);
    Py_DECREF(pysmtModule);
}

inline void MLBPythonGlobals::load_functions() {
    loadFileFunction = extract_local_function(MLBSMT2_FUNC_LOAD_FILE);
}

inline void MLBPythonGlobals::release_functions() {
    release_local_function(loadFileFunction);
}

inline PyObject* MLBPythonGlobals::extract_local_function(const std::string name) {
    PyObject* func = PyObject_GetAttrString(localModule, name.c_str());
    if (func == nullptr) { /* TODO: notify Error */ }
    if (!PyCallable_Check(func)) { /* TODO: notify Error */ }
    return func;
}

inline void MLBPythonGlobals::release_local_function(PyObject* f) {
    Py_DECREF(f);
}

static MLBPythonGlobals mlbPythonGlobals;

namespace mlbsmt2 {

    class MagicLiteralData {
        PyObject* pDataInstance;
    public:
        MagicLiteralData();
        ~MagicLiteralData();

        inline PyObject* getPyInstance() { return pDataInstance; }
    };

}

using namespace mlbsmt2;

MagicLiteralData::MagicLiteralData() {
    mlbPythonGlobals.initialize();
    // TODO: Create pDataInstance in Python
}

MagicLiteralData::~MagicLiteralData() {
    Py_DECREF(pDataInstance);
    mlbPythonGlobals.finalize();
}

/*>---------------------------------------<*/

MagicLiteralBuilder::MagicLiteralBuilder()
    : state(BuilderState::Initialized),
      data(new MagicLiteralData())
{}

MagicLiteralBuilder::~MagicLiteralBuilder() {
    data.release();
}

void MagicLiteralBuilder::loadSMTlib2File(const std::string filename) {
    PyObject* pLoadFunction = mlbPythonGlobals.get_loadfile_function();
    PyObject* pFileLoc = PyUnicode_DecodeFSDefault(filename.c_str());
    if (pFileLoc == nullptr) { /* TODO : Handle Error */ }
    PyObject* pArgs = PyTuple_New(2);
    PyTuple_SetItem(pArgs, 0, data->getPyInstance());
    PyTuple_SetItem(pArgs, 1, pFileLoc);
    PyObject_CallObject(pLoadFunction, pArgs);
    Py_DECREF(pFileLoc);
}

bool MagicLiteralBuilder::exploitData(DataExploitation e) {
    snlog::l_warn("Not implemented yet %£2");
    return false;
}
