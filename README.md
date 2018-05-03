# GPiD Framework

Generic framework for implicate generation modulo theories.
Uses a decomposition algorithm based on DPLL.

Description up to date for version 0.4.8.

# Dependencies

The framework is dependent on the following:

 - The Minisat SAT-Solver. This will be downloaded and patched at
   configuration time. Be careful however as Minisat itself requires
   the zlib library. If it is not available, the Minisat interface can
   be deactivated by passing the ```-DSKIP_SOLVERS=minisat``` at
   configuration time.
 - CVC4, SMT-Solver. Needs to be isntalled. The interface can be
   deactivated through the configuration option ```-DSKIP_SOLVERS=cvc4```.
 - Z3 min. version 4.6, SMT Solver. Needs to be installed with its
   cmake binder. The interface can be deactivated with the option
   ```-DSKIP_SOLVERS=z3```. ```LD-LIBRARY-PATH``` may need to be
   positioned for this to work at runtime.
 - Ruby-dev is required for generating the solvers interfaces.
 - Cxxopts is required for generating executables but will be
 downloaded and patched during configuration.
 - Googletest for tests. Also downloaded and patched during the
   configuration. Tests can be deactivated with the configuration
   option ```-D_BUILD_TESTS=OFF```.
 - Tooleval python library for running tests and benchmarking (Not yet
   available).

# Project structure #

 - ```framework``` : Core code of the implicate generator.
 - ```lib``` : Additional libraries required by the implicate generator.
 - ```solvers``` : Interfaces generator for various SMT-solvers.
 - ```test``` : Tests.
 - ```utils```, ```cmake``` : Various utilities for building and using the implicate
 generator.
 - ```exec``` : Code for generating the executables.

# Configuration and build #

The project is built via CMake.
The CMake configuration accepts the following specific options:

 - ```-DBUILD_DOC``` : Generate rules for creating a doxygen documentation.
 - ```-DBUILD_TESTS``` : Generate rules for building and executing tests. Uses the google-test framework.
 - ```-DSKIP_SOLVERS``` : A list of solvers not to generate targets
 for.
 - ```-DBUILD_TOOLEVAL``` : Generate rules for building tool
 evaluation scripts for the project.
 - ```-DBUILD_UTILITIES``` : Generate rules for building additional
 utilities for using the framework.
 - ```-DCOVERAGE_TOOLS``` : Generate rules and compile with code
 coverage instrumentation on unix.
 - ```-DGPID_INSTRUMENTATION``` : Instrument the framework to extract
 more data from executions at the cost of efficency.
 - ```-DSTATIC_EXECUTABLES``` : Use static executables format.
 - ```-DUSE_COLORS``` : Use ANSI Colors for printing on terminal.
 - ```-DDOT_AUTOCOMPILATION``` : Auto compile generated dot graphs.
 - ```-DMERGE_MINISAT_WRAPPERS``` : Merge minisat wrappers into their
   parent namespace.

The project builds a library and a related executable for every
interface provided as well as a global library and executable
containing all the configured interfaces.

# Usage

Executables are built in the ```bin``` subdirectory.

```gpid-gts -i <file> -g <generator> [-a <abd-generator> | -l <abd-file>]```

Or run ```gpid-gts -h``` for the complete option list.
