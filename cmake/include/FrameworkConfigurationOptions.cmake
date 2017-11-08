# ========== Project Options ==========
# ===== Targets selection =====
option(BUILD_TESTS "Build tests" ON)
option(COVERAGE_TOOLS "Configure and compile for code coverage reports" OFF)
option(GPID_INSTRUMENTATION "Activate gpid instrumentation toolset" OFF)
option(BUILD_DOC "Build documentation" ON)

# ===== Additional cosystems =====
option(USE_COLORS "Configure color print outputs" ON)
option(DOT_AUTOCOMPILATION "Configure Dot graphs autocompilation" ON)

# ===== Code system =====
option(MERGE_MINISAT_WRAPPERS "Merge Minisat wrappers into its original namespace" ON)

# ===== Solvers =====
option(TRUE_SOLVER_INTERFACE "Define an example solver class" ON)
option(MINISAT_SOLVER_INTERFACE "Define a propositional solver class based on minisat" ON)
option(CVC4_SOLVER_INTERFACE "Define a smt solver class based on cvc4" ON)
option(Z3_SOLVER_INTERFACE "Define a smt solver class based on z3" ON)
