# GPiD Framework and tools #

Generic framework for implicate generation modulo theories.

Description up to date for version 0.6.2.

# Content #

## GPiD Framework ##

The GPiD framework is a generic library one can use to solve abduction
problems modulo theories.

## Available Solver Interfaces ##

Some sample code binding usual SMT Solvers or SAT Solvers to it are
also provided. They assume that those solvers are available on the system.

## Utilities ##

The framework provides sample executables for performing
abduction using [1] with the previously introduced solver interfaces.

It also provide an utility to automatically generate abducible literals files. 

# Dependencies

## Required ##

The framework is dependent on the following to be configured and
built:

- CMake (min. version 3.5).
- A C++11 compiler handling Threads.
- A python3 interpreter with the following modules: colorama, pyyaml, jinja2

## Optional ##

- Doxygen for generating the documentation.
- Graphviz dot for generating insight graphs.

## Solver interfaces ##

- ZLib if building the Minisat Interface.
- CVC4 with its API and parsing library if building the CVC4
interface.
- Z3 (version 4.6.0 or 4.7.1) if building the Z3 interface.

## Tests ##

- The ToolEval python3 module for insight tests and benchmarks.
- Gcov for code coverage analyses. 

## Automatically downloaded and patch ##

The following dependencies are recovered and patched automatically by
the build tool chain:

- MiniSat (SAT Solver), patched for building its interface.
- The CxxOpts library for parsing options in sample executables.
- Google Tests for unit tests.

# Project structure #

 - ```framework``` : Core code of the implicate generator.
 - ```lib``` : Additional libraries required by the implicate generator.
 - ```solvers``` : Interfaces generator for various SMT-solvers.
 - ```test``` : Tests.
 - ```utils```, ```cmake``` : Various utilities for building and using the implicate
 generator.
 - ```exec``` : Code for generating the executables.

# Configuration, build and usage #

## Configuration ##

The project is built via CMake.
On Unix-like systems, run ```mkdir build && cd build && cmake ..```
The CMake configuration accepts the following specific options:

- ```-DSKIP_SOLVER_INTERFACE``` : A list of solvers not to generate targets
 for. 
- ```-DGPID_INSTRUMENTATION``` : Instrument the framework to extract
 more data from executions at the cost of efficency.  (Default OFF)
- ```-DBUILD_DOC``` : Generate rules for creating a doxygen documentation.  (Default ON)
- ```-DBUILD_TESTS``` : Generate rules for building and executing
   tests. Uses the google-test framework. (Default ON)
- ```-DBUILD_TOOLEVAL``` : Generate rules for building tool
 evaluation scripts for the project if Tooleval is available.  (Default ON)
- ```-DBUILD_UTILITIES``` : Generate rules for building additional
 utilities for using the framework.  (Default ON)
- ```-DCOVERAGE_TOOLS``` : Generate rules and compile with code
 coverage instrumentation on unix.  (Default OFF)
- ```-DSTATIC_EXECUTABLES``` : Use static executables format.  (Default ON)
- ```-DUSE_COLORS``` : Use ANSI Colors for printing on terminal.  (Default ON)
- ```-DDOT_AUTOCOMPILATION``` : Generate code allowing internal
 compilation of dot graphs.  (Default ON)

## Build ##

The project builds a library (gpid-core) containing the minimal
framework to generate implicates modulo theories using [1].
It also builds utilities for generating abducible literals and
implicate generators for the provided solver interfaces.

## Usage ##

Executables are built in the ```bin``` subdirectory.
For generating implicates using [1], run the following:
```gpid-impgen -i <file> -g <interface> [-a <abd-generator> | -l <abd-file>]```
or 
```gpid-impgen-<interface> -i <file> [-a <abd-generator> | -l <abd-file>]```.
Run ```gpid-impgen -h``` for the complete list of options.

If you wish to write your own solver interface, you can take a look at
the examples provided in the ```solvers``` subdirectory as well as the
documentation (built using Doxygen) of the ```Tisi``` solver, which
provides informations on all the elements that are required for such
an interface.

## Windows ##

The GPiD Framework is known to somehow compile and work on windows.
Last version compiled on windows: 0.6.2.

# Licence #

## Framework ##

The GPiD framework is <complete>.

## Executables ##

Impgen executables include code from their related solver interfaces and
are thus also subjet to the license of those.
Please check the corresponding lincences for details.

# References #

[1] M. Echenim, N. Peltier, and Y. Sellami. A generic framework for implicate generation modulo theories. In Automated Reasoning, International Joint Conference, IJCAR 2018, Proceedings, 2018.
