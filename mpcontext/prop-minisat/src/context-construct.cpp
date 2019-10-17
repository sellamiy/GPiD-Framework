#include <snlog/snlog.hpp>
#include <minisat/core/Dimacs.h>
#include <context-prop-minisat.hpp>

#define CONTEXT_PROP_CONSTRUCT_SRC

using namespace minpart;
using namespace minpart::prop;

const PartitionGeneratorOptions PropProblemContext::generate_partition_options() const {
    PartitionGeneratorOptions
        result(opts.c_blocksize, opts.c_depth, opts.p_blocksize, opts.p_depth,
               true, opts.random);
    return result;
}

PropProblemContext::PropProblemContext(const Options& opts)
    : opts(opts)
{
    solver.eliminate(true);
    solver.verbosity = 0;

    snlog::l_message() << "Loading " << opts.input_file << snlog::l_end;
    gzFile input_stream = gzopen(opts.input_file.c_str(), "rb"); // TODO: Handle input errors
    Minisat::parse_DIMACS(input_stream, solver);
    gzclose(input_stream);

    snlog::l_message() << "Recovering model..." << snlog::l_end;
    Minisat::vec<Minisat::Lit> dummy;
    Minisat::lbool ret = solver.solveLimited(dummy);
    if (ret != Minisat::l_True) {
        snlog::l_error() << "Unsat propositional formula" << snlog::l_end;
    }
    solver.model.copyTo(model);

    auto& hidden = snlog::l_message() << "Model is: ";
    for (int i = 0; i < model.size(); ++i)
        hidden << (model[i] == Minisat::l_Undef ?
                   "U" :
                   model[i] == Minisat::l_True ?
                   "T" : "F") << " ";
    hidden << snlog::l_end;
}
