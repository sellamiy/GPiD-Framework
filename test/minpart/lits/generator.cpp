#define MINPART_LITS_MMFP_RESULTS_GENERATOR_CPP

#include <ctime>
#include <snlog/snlog.hpp>
#include <minpart/minpart.hpp>
#include <minpart-contexts/literals.hpp>
#include <minpart/generic-partitions.hpp>

using namespace std;
using namespace snlog;
using namespace minpart;

// c-bsize c-depth p-bsize p-depth size maxd mind

#define MAX_SIZE     1000
#define SIZE_STEP    5000
#define MAX_MDEPTH   11
#define MDEPTH_STEP  1
#define MNDEPTH_STEP 1000
#define MAX_PSIZE    10
#define PSIZE_STEP   1000
#define COUNTER_C    100

template <class Context, class PartitionGenerator>
uint64_t shared_execute_main(const typename Context::Options& opts) {

    Context local(opts);
    PartitionGenerator generator(local.generate_partition_options());
    minpart::GSetEngine<Context> engine(local);
    stdutils::id_box<size_t> idbox(0);

    minpart::gsetid
        result = compute_minimal_part(engine, generator, idbox,
                                      engine.generate_full(),
                                      engine.generate_empty(local));

    if (!engine.is_coherent(result)) {
        snlog::l_error() << "Incoherent result detected" << snlog::l_end;
    }

    return engine.get_check_counter();
}


static int solve() {
    srand (time(NULL));

    literals::LiteralProblemOptions local; //local.{c_blocksize,c_depth,p_blocksize,p_depth}

    for (size_t size = 100; size < MAX_SIZE; size += SIZE_STEP) {
        for (size_t maxdepth = 1; maxdepth < MAX_MDEPTH; maxdepth += MDEPTH_STEP) {
            for (size_t mindepth = 0; mindepth < maxdepth; mindepth += MNDEPTH_STEP) {
                for (size_t partsize = 2; partsize < MAX_PSIZE; partsize += PSIZE_STEP) {
                    for (size_t count = 0; count < COUNTER_C; ++count) {
                        local.max_depth = maxdepth - 1;
                        local.c_blocksize = partsize;
                        local.p_blocksize = partsize;
                        // local.random = true;
                        //local.problem = random_vector(size, maxdepth, mindepth);
                        switch (maxdepth) {
                        case 1:
                            local.problem = random_vector(size, {1,5});
                            break;
                        case 2:
                            local.problem = random_vector(size, {1,5,20});
                            break;
                        case 3:
                            local.problem = random_vector(size, {1,5,20,25});
                            break;
                        case 4:
                            local.problem = random_vector(size, {1,5,20,25,30});
                            break;
                        case 5:
                            local.problem = random_vector(size, {1,5,20,25,30,30});
                            break;
                        case 6:
                            local.problem = random_vector(size, {1,5,20,25,30,30,30});
                            break;
                        case 7:
                            local.problem = random_vector(size, {1,5,20,25,30,30,30,30});
                            break;
                        case 8:
                            local.problem = random_vector(size, {1,5,20,25,30,30,30,30,30});
                            break;
                        case 9:
                            local.problem = random_vector(size, {1,5,20,25,30,30,30,30,30,30});
                            break;
                        case 10:
                            local.problem = random_vector(size, {1,5,20,25,30,30,30,30,30,30,30});
                            break;
                        }
                        uint64_t res =
                            shared_execute_main<literals::LiteralProblemContext,
                                                GenericPartitionGenerator>(local);
                        std::cout << "> " << size
                                  << ' ' << maxdepth
                                  << ' ' << mindepth
                                  << ' ' << partsize
                                  << ' ' << res
                                  << '\n';
                    }
                }
            }
        }
    }
    
    return EXIT_SUCCESS;
}

int main(int, char**) {

    try {
        return solve();
    } catch (std::exception& e) {
        l_internal() << "Unexpected throwable recovered" << l_end
                     << l_fatal << e.what() << l_end;
    }

    return EXIT_FAILURE;
}
