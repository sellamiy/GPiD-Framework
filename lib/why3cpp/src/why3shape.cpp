#define LIB_WHY3CPP__SHAPE_DETECTION__CPP

#include <array>
#include <fstream>
#include <sstream>
#include <snlog/snlog.hpp>
#include <why3cpp/why3shape.hpp>

namespace why3cpp {

    using strptr = std::shared_ptr<std::string>;

#define BUFFER_SIZE 128
    static const strptr execute(const std::string& command) {
        std::array<char, BUFFER_SIZE> buffer;
        std::stringstream result;
        std::shared_ptr<FILE> pipe(popen(command.c_str(), "r"), pclose);
        if (!pipe) {
            snlog::l_error() << "Why3 Proof command instantiation failure (popen)" << snlog::l_end;
            return strptr(new std::string());
        }
        while (!feof(pipe.get())) {
            if (fgets(buffer.data(), 128, pipe.get()) != nullptr) {
                result << buffer.data();
            }
        }
        return strptr(new std::string(result.str()));
    }

    static bool drv_generate = false;

    static void generate_shape_driver(const std::string& loc) {
        if (drv_generate) return;
        std::ofstream ofs(loc);
        if (!ofs.is_open()) {
            snlog::l_fatal() << "Why3 Shape driver cannot be written to " << loc << snlog::l_end;
        }
        ofs << "(* lib why3cpp why3 files shape detector - generated why3 driver *)" << '\n'
            << '\n'
            << "prelude \";; " << WHY3CPP_SHAPE_ANCHOR_DATA << "\"" << '\n'
            << '\n'
            << "printer \"why3\"" << '\n';
        ofs.close();
        drv_generate = true;
    }

    static const std::string generate_shape_detection_command
    (const std::string& filename, const std::string& drv) {
        std::stringstream cmd;
        cmd << WHY3_EXECUTABLE << " prove -a split_vc -D " << drv << " " << filename;
        return cmd.str();
    }

    extern ProblemShape detect_shape(const std::string& filename) {
        generate_shape_driver(WHY3_SHAPE_DRIVER_LOC);
        const strptr result = execute(generate_shape_detection_command(filename, WHY3_SHAPE_DRIVER_LOC));
        return parse_shape_data(*result);
    }

}
